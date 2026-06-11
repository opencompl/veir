# LLZK Felt Porting Slides

This is a small standalone VersoSlides deck for a VEIR maintainer discussion.
It summarizes the LLZK Felt dialect port, the drop-in replacement roadmap, and
the upstream VEIR ergonomics that would make future C++ MLIR dialect ports more
systematic.

The deck source is:

- `LlzkFeltPortingSlides/Slides.lean`

## Build

From this directory:

```bash
lake update
lake build
lake exe llzk-felt-porting-slides
python3 -m http.server -d _slides
```

Then open the served `index.html`.

Notes:

- This project intentionally lives under `docs/slides/` so it does not modify
  the main VEIR Lake package.
- The first build downloads `leanprover/verso-slides` and its dependencies.
- VersoSlides generates offline reveal.js output under `_slides/`.
