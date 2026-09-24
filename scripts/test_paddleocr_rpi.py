import paddle
from paddleocr import PaddleOCR


print(f"paddle={paddle.__version__}")
PaddleOCR(
    lang="en",
    use_doc_orientation_classify=False,
    use_doc_unwarping=False,
    use_textline_orientation=False,
)
print("ocr_ready")