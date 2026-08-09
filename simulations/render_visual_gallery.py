import html
import os
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT_DIR = ROOT / "visuals"
OUT_DIR.mkdir(exist_ok=True)

def collect_images():
    images = []
    for base in [ROOT, ROOT / "simulations"]:
        if not base.exists():
            continue
        for pattern in ("*.png", "*.jpg", "*.jpeg"):
            images.extend(base.rglob(pattern))

    seen = set()
    result = []
    for path in sorted(images):
        if not path.is_file():
            continue
        if OUT_DIR in path.parents:
            continue
        key = str(path.resolve())
        if key in seen:
            continue
        seen.add(key)
        result.append(path)

    return result

def copy_images(images):
    copied = []
    for source in images:
        rel = source.relative_to(ROOT)
        dest = OUT_DIR / rel.as_posix().replace("/", "__")
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, dest)
        copied.append(dest)
    return copied

def write_gallery(copied_images):
    cards = []
    for path in copied_images:
        rel = path.relative_to(OUT_DIR).as_posix()
        title = path.stem.replace("_", " ").title()
        # Wrapped image inside a target='_blank' link to expand image on click
        cards.append(
            f"<div class='card'>"
            f"<h3>{html.escape(title)}</h3>"
            f"<a href='{html.escape(rel)}' target='_blank' title='Click to view full size'>"
            f"<img src='{html.escape(rel)}' alt='{html.escape(title)}'>"
            f"</a>"
            f"<p>{html.escape(rel)}</p>"
            f"</div>"
        )

    html_text = f"""<!doctype html>
<html>
<head>
  <meta charset='utf-8'>
  <title>Epsilon Framework Visual Gallery</title>
  <style>
    body {{ font-family: Arial, sans-serif; margin: 24px; background: #111; color: #eee; }}
    .grid {{ display: grid; grid-template-columns: repeat(auto-fit, minmax(360px, 1fr)); gap: 24px; }}
    .card {{ background: #1d1d1d; border: 1px solid #333; border-radius: 8px; padding: 14px; transition: transform 0.15s ease; }}
    .card:hover {{ transform: translateY(-2px); border-color: #00f2fe; }}
    a {{ display: block; text-decoration: none; }}
    img {{ width: 100%; height: auto; border-radius: 6px; margin-top: 8px; cursor: pointer; }}
    h3 {{ margin: 0 0 8px 0; color: #fff; font-size: 16px; }}
    p {{ font-size: 12px; color: #888; word-break: break-all; margin-top: 8px; }}
  </style>
</head>
<body>
  <h1>Epsilon Framework Visual Gallery</h1>
  <p style="color: #aaa; margin-bottom: 20px;">Click any image card to open high-resolution plot in full size.</p>
  <div class='grid'>
    {''.join(cards)}
  </div>
</body>
</html>
"""

    (OUT_DIR / "index.html").write_text(html_text, encoding="utf-8")

def open_gallery():
    index_file = OUT_DIR / "index.html"
    if sys.platform == "darwin":
        subprocess.run(["open", str(index_file)], check=False)
    elif sys.platform.startswith("linux"):
        subprocess.run(["xdg-open", str(index_file)], check=False)
    elif sys.platform == "win32":
        os.startfile(str(index_file))  # type: ignore[attr-defined]

def main():
    images = collect_images()
    copied = copy_images(images)
    write_gallery(copied)
    open_gallery()

if __name__ == "__main__":
    main()