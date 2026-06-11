import VersoSlides
import LlzkFeltPortingSlides.Slides

open VersoSlides

def main : IO UInt32 :=
  slidesMain
    (config := { theme := "white", slideNumber := true, transition := "slide" })
    (doc := %doc LlzkFeltPortingSlides.Slides)
