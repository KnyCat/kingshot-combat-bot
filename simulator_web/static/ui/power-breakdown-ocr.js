(() => {
  document.querySelectorAll("[data-power-ocr]").forEach(uploader => {
    const input = uploader.querySelector('input[type="file"]');
    const button = uploader.querySelector("button");
    const status = uploader.querySelector("[data-power-ocr-status]");

    async function extract() {
      const file = input.files?.[0];
      if (!file) {
        input.click();
        return;
      }
      button.disabled = true;
      input.disabled = true;
      uploader.classList.add("is-reading");
      status.textContent = "Reading screenshot...";
      const data = new FormData();
      data.append("image", file);
      try {
        const response = await fetch(uploader.dataset.endpoint, {method: "POST", body: data});
        const contentType = response.headers.get("content-type") || "";
        if (!contentType.includes("application/json")) {
          throw new Error(`OCR service returned HTTP ${response.status}. Please try again.`);
        }
        const payload = await response.json();
        if (!response.ok || !payload.ok) throw new Error(payload.message || "Could not read the screenshot.");
        Object.entries(payload.fields || {}).forEach(([name, value]) => {
          const field = document.querySelector(`[name="${name}"]`);
          if (field) {
            field.value = String(value);
            field.dispatchEvent(new Event("input", {bubbles: true}));
          }
        });
        status.textContent = "Seven power values detected. Review them before submitting.";
      } catch (error) {
        status.textContent = error instanceof Error ? error.message : "Could not read the screenshot.";
      } finally {
        button.disabled = false;
        input.disabled = false;
        uploader.classList.remove("is-reading");
      }
    }

    input.addEventListener("change", extract);
    button.addEventListener("click", extract);
  });
})();