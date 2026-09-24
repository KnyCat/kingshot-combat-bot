VALORA_MARCH_BONUS = {level: level * 3000 for level in range(11)}
BISON_MARCH_BONUS = {level: level * 1500 for level in range(11)}
CASSIA_MARCH_BONUS = {level: level * 5000 for level in range(21)}
BOOSTER_PERCENTAGES = {0, 10, 20}


def calculate_buffed_march_capacity(
    base_capacity: int,
    valora_level: int,
    cassia_level: int,
    bison_level: int,
    booster_percent: int,
) -> int:
    if base_capacity <= 0:
        raise ValueError("March capacity must be positive.")
    if valora_level not in VALORA_MARCH_BONUS:
        raise ValueError("Valora level must be between 0 and 10.")
    if cassia_level not in CASSIA_MARCH_BONUS:
        raise ValueError("Cassia level must be between 0 and 20.")
    if bison_level not in BISON_MARCH_BONUS:
        raise ValueError("Bison level must be between 0 and 10.")
    if booster_percent not in BOOSTER_PERCENTAGES:
        raise ValueError("Booster must be 0%, 10% or 20%.")

    boosted_base = round(base_capacity * (1 + booster_percent / 100))
    return (
        boosted_base
        + VALORA_MARCH_BONUS[valora_level]
        + CASSIA_MARCH_BONUS[cassia_level]
        + BISON_MARCH_BONUS[bison_level]
    )