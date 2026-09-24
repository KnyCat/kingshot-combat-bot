from __future__ import annotations

import io
import os
import re
import sys
from collections import Counter, deque
from typing import Any


POWER_PATTERN = re.compile(r"(?<!\d)(\d{1,3}(?:[.,]\d{3})+|\d{3,8})(?!\d)")
MIN_AC_POWER = 500
MAX_AC_POWER = 99_999


def _number(value: str) -> int:
    return int(re.sub(r"\D", "", value))


def parse_ac_rival_tokens(tokens: list[dict[str, Any]], image_width: int, side: str = "right") -> list[dict[str, Any]]:
    side = "left" if side == "left" else "right"
    positions = []
    powers = []
    for token in tokens:
        text = str(token.get("text") or "").strip()
        confidence = float(token.get("confidence", 0) or 0)
        if not text or confidence < 10:
            continue
        center_y = float(token.get("top", 0)) + float(token.get("height", 0)) / 2
        left = float(token.get("left", 0))
        if text.isdigit() and 1 <= int(text) <= 20:
            positions.append({**token, "position": int(text), "center_y": center_y})
        for match in POWER_PATTERN.finditer(text):
            power = _number(match.group(1))
            if MIN_AC_POWER <= power <= MAX_AC_POWER:
                powers.append({**token, "power": power, "center_y": center_y})

    rivals: dict[int, dict[str, Any]] = {}
    for power_token in powers:
        nearby_positions = [
            position for position in positions
            if abs(position["center_y"] - power_token["center_y"]) <= max(
                float(position.get("height", 0)),
                float(power_token.get("height", 0)),
                20,
            ) * 6
            and (
                float(position.get("left", 0)) < float(power_token.get("left", 0))
                if side == "left"
                else float(position.get("left", 0)) > float(power_token.get("left", 0))
            )
        ]
        if not nearby_positions:
            continue
        position_token = min(nearby_positions, key=lambda item: abs(item["center_y"] - power_token["center_y"]))
        position = int(position_token["position"])
        power = int(power_token["power"])
        power_digits = str(power)
        if len(power_digits) == 5 and power_digits[1] == "1":
            corrected_power = int(power_digits[0] + power_digits[2:])
            if 500 <= corrected_power <= 9_999:
                power = corrected_power
        candidate = {"position": position, "name": f"Rival {position}", "power": power}
        current = rivals.get(position)
        if current is None or candidate["power"] > current["power"]:
            rivals[position] = candidate

    return [rivals[position] for position in sorted(rivals)]


def _extract_ac_rivals_legacy(image_bytes: bytes, side: str = "right") -> list[dict[str, Any]]:
    import pytesseract
    from PIL import Image, ImageEnhance, ImageFilter, ImageOps

    if sys.platform == "win32":
        for tesseract_path in (
            r"C:\Program Files\Tesseract-OCR\tesseract.exe",
            r"C:\Program Files (x86)\Tesseract-OCR\tesseract.exe",
        ):
            if os.path.exists(tesseract_path):
                pytesseract.pytesseract.tesseract_cmd = tesseract_path
                break

    image = Image.open(io.BytesIO(image_bytes)).convert("RGB")
    width, height = image.size
    side = "left" if side == "left" else "right"
    import numpy as np

    def read_column(box: tuple[int, int, int, int], whitelist: str, psms: tuple[int, ...]) -> list[dict[str, Any]]:
        box_height = max(1, box[3] - box[1])
        column = image.crop(box).resize(
            ((box[2] - box[0]) * 3, box_height * 3),
            Image.Resampling.LANCZOS,
        )
        gray = ImageOps.grayscale(column)
        enhanced = ImageEnhance.Sharpness(ImageEnhance.Contrast(gray).enhance(2.4)).enhance(2.5)
        thresholded = ImageOps.autocontrast(enhanced).point(lambda value: 255 if value > 160 else 0)
        color_pixels = np.asarray(column.convert("RGB"))
        cream_mask = (
            (color_pixels[:, :, 0] > 175)
            & (color_pixels[:, :, 1] > 145)
            & (color_pixels[:, :, 2] < 225)
            & (color_pixels[:, :, 0] > color_pixels[:, :, 2] * 1.08)
        )
        cream_digits = Image.fromarray(np.where(cream_mask, 0, 255).astype(np.uint8), mode="L")
        variants = [enhanced, ImageOps.invert(enhanced), thresholded, ImageOps.invert(thresholded), cream_digits]
        tokens: list[dict[str, Any]] = []
        for processed in variants:
            for psm in psms:
                data = pytesseract.image_to_data(
                    processed.filter(ImageFilter.SHARPEN),
                    config=f"--psm {psm} --oem 3 -c tessedit_char_whitelist={whitelist}",
                    output_type=pytesseract.Output.DICT,
                )
                fragments = [str(text).strip() for text in data.get("text", []) if str(text).strip()]
                if box_height < height * 0.25 and fragments:
                    tokens.append({
                        "text": "".join(fragments),
                        "center_y": (box[1] + box[3]) / 2,
                    })
                for index, text in enumerate(data.get("text", [])):
                    cleaned = str(text).strip()
                    if not cleaned or float(data["conf"][index] or 0) < 5:
                        continue
                    tokens.append({
                        "text": cleaned,
                        "left": box[0] + float(data["left"][index]) / 3,
                        "top": box[1] + float(data["top"][index]) / 3,
                        "width": float(data["width"][index]) / 3,
                        "height": float(data["height"][index]) / 3,
                        "center_x": box[0] + (float(data["left"][index]) + float(data["width"][index]) / 2) / 3,
                        "center_y": box[1] + (float(data["top"][index]) + float(data["height"][index]) / 2) / 3,
                    })
        return tokens

    pixels = np.asarray(image)
    red = pixels[:, :, 0]
    green = pixels[:, :, 1]
    blue = pixels[:, :, 2]
    if side == "left":
        mask = (red >= 35) & (red <= 115) & (green >= 50) & (green <= 135) & (blue >= 95) & (blue <= 195) & (blue > red * 1.25)
    else:
        mask = (red >= 115) & (red <= 210) & (green >= 35) & (green <= 125) & (blue >= 45) & (blue <= 145) & (red > green * 1.35)

    visited = np.zeros(mask.shape, dtype=bool)
    position_tokens = []
    minimum_size = max(18, int(width * 0.055))
    maximum_size = max(minimum_size + 1, int(width * 0.16))
    for start_y, start_x in zip(*np.nonzero(mask & ~visited)):
        if visited[start_y, start_x]:
            continue
        queue = deque([(int(start_x), int(start_y))])
        visited[start_y, start_x] = True
        points = []
        while queue:
            x, y = queue.popleft()
            points.append((x, y))
            for next_x, next_y in ((x - 1, y), (x + 1, y), (x, y - 1), (x, y + 1)):
                if 0 <= next_x < width and 0 <= next_y < height and mask[next_y, next_x] and not visited[next_y, next_x]:
                    visited[next_y, next_x] = True
                    queue.append((next_x, next_y))
        if len(points) < minimum_size * minimum_size * 0.25:
            continue
        xs = [point[0] for point in points]
        ys = [point[1] for point in points]
        left, right = min(xs), max(xs) + 1
        top, bottom = min(ys), max(ys) + 1
        component_width = right - left
        component_height = bottom - top
        if not (minimum_size <= component_width <= maximum_size and minimum_size <= component_height <= maximum_size):
            continue
        if not 0.65 <= component_width / component_height <= 1.45:
            continue
        circle_tokens = read_column((left, top, right, bottom), "0123456789", (10,))
        values = []
        for token in circle_tokens:
            digits = re.sub(r"\D", "", token["text"])
            if digits and 1 <= int(digits) <= 20:
                values.append(int(digits))
        if not values:
            continue
        value_counts = Counter(values)
        position = min(value_counts, key=lambda value: (-value_counts[value], -len(str(value)), -value))
        if position < 10 and position + 10 in value_counts:
            position += 10
        position_tokens.append({
            "position": position,
            "left": float(left),
            "top": float(top),
            "width": float(component_width),
            "height": float(component_height),
            "center_x": (left + right) / 2,
            "center_y": (top + bottom) / 2,
        })
    positions: list[dict[str, Any]] = []
    for token in sorted(position_tokens, key=lambda item: item["center_y"]):
        if positions and token["position"] == positions[-1]["position"] and abs(token["center_y"] - positions[-1]["center_y"]) < 12:
            continue
        positions.append(token)
    rivals: dict[int, dict[str, Any]] = {}
    debug_powers: list[tuple[int, int | None]] = []
    for position in positions:
        anchor_height = max(float(position["height"]), width * 0.04)
        if side == "left":
            power_left = float(position["left"]) + float(position["width"]) + anchor_height * 0.35
            power_right = float(position["left"]) + float(position["width"]) + anchor_height * 1.8
        else:
            power_left = float(position["left"]) - anchor_height * 1.55
            power_right = float(position["left"]) - anchor_height * 0.25
        power_box = (
            max(0, int(power_left)),
            max(0, int(position["center_y"] + anchor_height * 0.8)),
            min(width, int(power_right)),
            min(height, int(position["center_y"] + anchor_height * 1.9)),
        )
        candidates = []
        for token in read_column(power_box, "0123456789.,", (7,)):
            for match in POWER_PATTERN.finditer(token["text"]):
                power = _number(match.group(1))
                if MIN_AC_POWER <= power <= MAX_AC_POWER:
                    candidates.append(power)
        if not candidates:
            debug_powers.append((int(position["position"]), None))
            continue
        counts = Counter(candidates)
        power = min(counts, key=lambda value: (-counts[value], len(str(value)), value))
        debug_powers.append((int(position["position"]), int(power)))
        rival_position = int(position["position"])
        candidate = {"position": rival_position, "name": f"Rival {rival_position}", "power": int(power)}
        current = rivals.get(rival_position)
        if current is None or candidate["power"] > current["power"]:
            rivals[rival_position] = candidate
    print(
        f"AC OCR side={side} positions={[(item['position'], round(item['center_y'])) for item in positions]} "
        f"row_powers={debug_powers}",
        flush=True,
    )
    return [rivals[position] for position in sorted(rivals)]


def extract_ac_rivals(image_bytes: bytes, side: str = "right") -> list[dict[str, Any]]:
    import pytesseract
    from PIL import Image, ImageEnhance, ImageFilter, ImageOps

    if sys.platform == "win32":
        for tesseract_path in (
            r"C:\Program Files\Tesseract-OCR\tesseract.exe",
            r"C:\Program Files (x86)\Tesseract-OCR\tesseract.exe",
        ):
            if os.path.exists(tesseract_path):
                pytesseract.pytesseract.tesseract_cmd = tesseract_path
                break

    image = Image.open(io.BytesIO(image_bytes)).convert("RGB")
    width, height = image.size
    side = "left" if side == "left" else "right"
    scaled = image.resize((width * 2, height * 2), Image.Resampling.LANCZOS)
    gray = ImageOps.grayscale(scaled)
    enhanced = ImageEnhance.Sharpness(ImageEnhance.Contrast(gray).enhance(2.2)).enhance(2.0)
    thresholded = ImageOps.autocontrast(enhanced).point(lambda value: 255 if value > 160 else 0)
    variants = ((enhanced, 11), (enhanced, 6), (thresholded, 11), (ImageOps.invert(thresholded), 11))
    tokens: list[dict[str, Any]] = []

    for variant_index, (processed, psm) in enumerate(variants):
        data = pytesseract.image_to_data(
            processed.filter(ImageFilter.SHARPEN),
            config=f"--psm {psm} --oem 3",
            output_type=pytesseract.Output.DICT,
        )
        for index, raw_text in enumerate(data.get("text", [])):
            text = str(raw_text).strip()
            confidence = float(data["conf"][index] or 0)
            if not text or confidence < 5:
                continue
            left = float(data["left"][index]) / 2
            top = float(data["top"][index]) / 2
            token_width = float(data["width"][index]) / 2
            token_height = float(data["height"][index]) / 2
            tokens.append({
                "text": text,
                "digits": re.sub(r"\D", "", text),
                "confidence": round(confidence, 1),
                "left": left,
                "top": top,
                "width": token_width,
                "height": token_height,
                "center_x": left + token_width / 2,
                "center_y": top + token_height / 2,
                "variant": variant_index,
            })

    numeric_tokens = [token for token in tokens if token["digits"]]
    print(
        "AC OCR global_tokens="
        + repr([
            (token["text"], token["digits"], round(token["center_x"]), round(token["center_y"]), round(token["height"]), token["confidence"])
            for token in numeric_tokens
        ]),
        flush=True,
    )

    selected_half = [
        token for token in numeric_tokens
        if (token["center_x"] < width / 2 if side == "left" else token["center_x"] > width / 2)
    ]
    position_candidates = [
        token for token in selected_half
        if 1 <= int(token["digits"]) <= 20 and token["height"] >= width * 0.025
    ]
    positions: list[dict[str, Any]] = []
    for token in sorted(position_candidates, key=lambda item: item["center_y"]):
        duplicate = next(
            (item for item in positions if abs(item["center_y"] - token["center_y"]) < max(item["height"], token["height"]) * 0.5),
            None,
        )
        if duplicate:
            if token["confidence"] > duplicate["confidence"]:
                positions[positions.index(duplicate)] = token
            continue
        positions.append(token)

    power_side_tokens = [
        token for token in numeric_tokens
        if (width * 0.08 < token["center_x"] < width * 0.44 if side == "left" else width * 0.56 < token["center_x"] < width * 0.92)
        and token["height"] >= width * 0.025
    ]
    power_rows: list[list[dict[str, Any]]] = []
    for token in sorted(power_side_tokens, key=lambda item: item["center_y"]):
        row = next((items for items in power_rows if abs(items[0]["center_y"] - token["center_y"]) < width * 0.035), None)
        if row is None:
            power_rows.append([token])
        else:
            row.append(token)

    def normalize_power_candidates(row: list[dict[str, Any]]) -> list[int]:
        values = []
        for token in row:
            digits = token["digits"]
            candidates = [digits]
            if len(digits) >= 5:
                candidates.extend(digits[index:] for index in range(1, len(digits) - 3))
                candidates.extend(digits[:index] + digits[index + 1:] for index in range(len(digits)))
            for candidate_digits in candidates:
                value = int(candidate_digits)
                if MIN_AC_POWER <= value <= 9_999:
                    values.append(value)
        return values

    rivals: dict[int, dict[str, Any]] = {}
    debug_rows = []
    for row in power_rows:
        row_y = sum(token["center_y"] for token in row) / len(row)
        position = min(positions, key=lambda item: abs((item["center_y"] + max(item["height"], width * 0.06) * 1.15) - row_y), default=None)
        if position is None or abs((position["center_y"] + max(position["height"], width * 0.06) * 1.15) - row_y) > width * 0.16:
            continue
        position_value = int(position["digits"])
        power_candidates = normalize_power_candidates(row)
        debug_rows.append((position_value, [(value, token["text"]) for value in power_candidates for token in row[:1]]))
        if not power_candidates:
            continue
        counts = Counter(power_candidates)
        power = min(counts, key=lambda value: (-counts[value], abs(len(str(value)) - 4), value))
        candidate = {"position": position_value, "name": f"Rival {position_value}", "power": power}
        current = rivals.get(position_value)
        if current is None or power > current["power"]:
            rivals[position_value] = candidate

    print(f"AC OCR global side={side} positions={[int(item['digits']) for item in positions]} rows={debug_rows}", flush=True)
    return [rivals[position] for position in sorted(rivals)]


def merge_ac_rivals(groups: list[list[dict[str, Any]]]) -> list[dict[str, Any]]:
    merged: dict[int, dict[str, Any]] = {}
    for group in groups:
        for rival in group:
            position = int(rival["position"])
            current = merged.get(position)
            if current is None or int(rival["power"]) > int(current["power"]):
                merged[position] = rival
    return [merged[position] for position in sorted(merged)]