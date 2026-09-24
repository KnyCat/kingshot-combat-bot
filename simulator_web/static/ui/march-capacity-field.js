(() => {
  const field = name => document.querySelector(`[name="${name}"]`);
  const base = field("march_capacity_base");
  const valora = field("valora_level");
  const cassia = field("cassia_level");
  const bison = field("bison_level");
  const booster = field("march_booster_percent");
  const result = field("march_capacity_buffed");
  if (!base || !valora || !cassia || !bison || !booster || !result) return;

  const calculate = () => {
    const baseCapacity = Number.parseInt(base.value, 10);
    if (!Number.isFinite(baseCapacity) || baseCapacity <= 0) {
      result.value = "";
      return;
    }
    const boosterPercent = Number.parseInt(booster.value, 10) || 0;
    result.value = String(
      Math.round(baseCapacity * (1 + boosterPercent / 100))
      + (Number.parseInt(valora.value, 10) || 0) * 3000
      + (Number.parseInt(cassia.value, 10) || 0) * 5000
      + (Number.parseInt(bison.value, 10) || 0) * 1500
    );
  };

  [base, valora, cassia, bison, booster].forEach(control => {
    control.addEventListener("input", calculate);
    control.addEventListener("change", calculate);
  });
  calculate();
})();