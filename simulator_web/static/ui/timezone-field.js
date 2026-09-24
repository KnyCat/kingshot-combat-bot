(() => {
  const fallbackZones = [
    "UTC", "Africa/Cairo", "Africa/Johannesburg", "America/Argentina/Buenos_Aires",
    "America/Bogota", "America/Chicago", "America/Los_Angeles", "America/Mexico_City",
    "America/New_York", "America/Sao_Paulo", "America/Toronto", "Asia/Dubai",
    "Asia/Hong_Kong", "Asia/Jakarta", "Asia/Riyadh", "Asia/Seoul", "Asia/Shanghai",
    "Asia/Singapore", "Asia/Tokyo", "Australia/Sydney", "Europe/Berlin", "Europe/Istanbul",
    "Europe/London", "Europe/Madrid", "Europe/Moscow", "Europe/Paris", "Pacific/Auckland"
  ];

  function offsetFor(timeZone) {
    try {
      const part = new Intl.DateTimeFormat("en", {
        timeZone,
        timeZoneName: "shortOffset"
      }).formatToParts(new Date()).find(item => item.type === "timeZoneName");
      return (part?.value || "UTC").replace("GMT", "UTC");
    } catch (_error) {
      return "UTC";
    }
  }

  function populate(select) {
    const detected = Intl.DateTimeFormat().resolvedOptions().timeZone || "UTC";
    const saved = select.dataset.value || select.value;
    const supported = typeof Intl.supportedValuesOf === "function"
      ? Intl.supportedValuesOf("timeZone")
      : fallbackZones;
    const zones = [...new Set([saved, detected, ...supported].filter(Boolean))].sort();
    select.replaceChildren(new Option("Choose time zone", ""));
    zones.forEach(zone => select.add(new Option(`${zone} (${offsetFor(zone)})`, zone)));
    select.value = saved || detected;
  }

  document.querySelectorAll("select.js-timezone").forEach(populate);
})();