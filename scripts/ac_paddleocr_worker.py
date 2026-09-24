from __future__ import annotations

import json
import re
import sys
from pathlib import Path

from paddleocr import PaddleOCR
from PIL import Image


def extract(
    path: str,
    side: str,
    ocr: PaddleOCR,
    known_positions: dict[str, int],
    last_position: list[int],
) -> list[dict[str, object]]:
    results = list(ocr.predict(path))
    if not results:
        return []
    payload = results[0].json
    data = payload.get("res", payload)
    texts = data.get("rec_texts", [])
    scores = data.get("rec_scores", [])
    boxes = data.get("rec_boxes", data.get("rec_polys", []))
    tokens = []
    for text, score, box in zip(texts, scores, boxes):
        points = box.tolist() if hasattr(box, "tolist") else box
        if len(points) == 4 and not isinstance(points[0], (list, tuple)):
            left, top, right, bottom = map(float, points)
        else:
            xs = [float(point[0]) for point in points]
            ys = [float(point[1]) for point in points]
            left, top, right, bottom = min(xs), min(ys), max(xs), max(ys)
        digits = re.sub(r"\D", "", str(text))
        tokens.append({
            "text": str(text),
            "digits": digits,
            "score": float(score),
            "left": left,
            "top": top,
            "right": right,
            "bottom": bottom,
            "center_x": (left + right) / 2,
            "center_y": (top + bottom) / 2,
            "height": bottom - top,
        })
    with Image.open(path) as image:
        image_width = float(image.width)
    selected = [token for token in tokens if (token["center_x"] < image_width / 2 if side == "left" else token["center_x"] > image_width / 2)]
    edge_positions = [
        token for token in selected
        if token["digits"]
        and 1 <= int(token["digits"]) <= 20
        and (token["center_x"] < image_width * 0.16 if side == "left" else token["center_x"] > image_width * 0.84)
        and token["height"] >= image_width * 0.045
    ]
    powers = [
        token for token in selected
        if re.fullmatch(r"\D*\d[.,]\d{3}\D*", token["text"])
        and 500 <= int(token["digits"]) <= 9999
        and (image_width * 0.16 < token["center_x"] < image_width * 0.43 if side == "left" else image_width * 0.57 < token["center_x"] < image_width * 0.84)
    ]
    powers.sort(key=lambda token: token["center_y"])
    rivals: dict[int, dict[str, object]] = {}
    parsed_rows: list[dict[str, object]] = []
    for power_token in powers:
        position_gap_min = image_width * 0.035
        position_gap_max = image_width * 0.17
        expected_position_gap = image_width * 0.13
        row_positions = [
            position for position in edge_positions
            if position_gap_min <= power_token["center_y"] - position["center_y"] <= position_gap_max
        ]
        position_value = int(min(
            row_positions,
            key=lambda token: abs(power_token["center_y"] - token["center_y"] - expected_position_gap),
        )["digits"]) if row_positions else 0
        name_candidates = [
            token for token in selected
            if re.search(r"[^\W\d_]", token["text"], re.UNICODE)
            and image_width * 0.01 <= power_token["center_y"] - token["center_y"] <= image_width * 0.085
            and abs(token["center_x"] - power_token["center_x"]) < image_width * 0.20
            and token["text"].upper() not in {"WIN", "VS"}
        ]
        name = max(name_candidates, key=lambda token: (token["score"], len(token["text"])), default={"text": ""})["text"].strip()
        name_key = re.sub(r"\W", "", name).casefold()
        parsed_rows.append({
            "position": position_value,
            "name": name,
            "name_key": name_key,
            "power": int(power_token["digits"][-4:]),
            "center_y": power_token["center_y"],
        })

    parsed_rows.sort(key=lambda row: float(row["center_y"]))
    anchored_rows = [(index, int(row["position"])) for index, row in enumerate(parsed_rows) if row["position"]]
    for index, row in enumerate(parsed_rows):
        position_value = int(row["position"])
        name = str(row["name"])
        name_key = str(row["name_key"])
        if position_value:
            if name_key:
                known_positions[name_key] = position_value
        elif name_key and name_key in known_positions:
            position_value = known_positions[name_key]
        else:
            nearest_anchor = min(anchored_rows, key=lambda anchor: abs(anchor[0] - index), default=None)
            if nearest_anchor:
                position_value = nearest_anchor[1] + index - nearest_anchor[0]
            if not 1 <= position_value <= 20:
                continue
            if name_key:
                known_positions[name_key] = position_value
        power = int(row["power"])
        candidate = {"position": position_value, "name": name or f"Rival {position_value}", "power": power}
        current = rivals.get(position_value)
        if current is None or power > int(current["power"]):
            rivals[position_value] = candidate
    print(f"PaddleOCR file={Path(path).name} tokens={[(t['text'], round(t['center_x']), round(t['center_y'])) for t in tokens]}", file=sys.stderr)
    return [rivals[position] for position in sorted(rivals)]


def main() -> None:
    side = sys.argv[1]
    paths = sys.argv[2:]
    ocr = PaddleOCR(
        lang="en",
        text_detection_model_name="PP-OCRv5_mobile_det",
        text_recognition_model_name="PP-OCRv5_mobile_rec",
        use_doc_orientation_classify=False,
        use_doc_unwarping=False,
        use_textline_orientation=False,
        enable_mkldnn=False,
        cpu_threads=2,
    )
    known_positions: dict[str, int] = {}
    last_position = [0]
    print(json.dumps([extract(path, side, ocr, known_positions, last_position) for path in paths], ensure_ascii=True))


if __name__ == "__main__":
    main()