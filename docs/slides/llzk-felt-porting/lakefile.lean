import Lake

open Lake DSL

package llzk_felt_porting_slides where
  version := v!"0.1.0"

require «verso-slides» from git
  "https://github.com/leanprover/verso-slides.git" @ "main"

lean_lib LlzkFeltPortingSlides

@[default_target]
lean_exe «llzk-felt-porting-slides» where
  root := `Main
