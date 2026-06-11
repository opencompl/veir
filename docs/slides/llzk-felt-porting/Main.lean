import VersoSlides
import LlzkFeltPortingSlides.Slides

open VersoSlides

def compactCss : CssFile where
  filename := "compact.css"
  contents := ⟨include_str "compact.css"⟩

def main : IO UInt32 :=
  slidesMain
    (config := {
      theme := "white",
      slideNumber := true,
      transition := "slide",
      width := 1280,
      height := 720,
      margin := 0.035,
      center := false,
      extraCss := #[compactCss]
    })
    (doc := %doc LlzkFeltPortingSlides.Slides)
