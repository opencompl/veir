import Veir.Dialects.LLVM.Interpreter
import Veir.Interpreter.CTreeRunner

/-!
  In CTrees, freezing a poison pointer chooses a pointer, which the runner's choice handler
  resolves.
-/

open Veir

/-- Freezing a poison pointer. -/
private def freezePoisonPointer : Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction) :=
  Llvm.interpretOpCTree .freeze (by exact ()) #[] #[.addr .poison] #[] .empty

/-- The results of a run. -/
private def results : Interp (Array RuntimeValue × MemoryState × Option ControlFlowAction) → String
  | .ok (values, _, _) => toString values
  | _ => "no result"

-- By default, the runner chooses the null pointer.
/-- info: "#[ptr(0, 0)]" -/
#guard_msgs in
#eval results freezePoisonPointer.run

-- Any other pointer may be chosen too, here the wildcard pointer at address 16.
/-- info: "#[ptr(*, 16)]" -/
#guard_msgs in
#eval results (freezePoisonPointer.run fun | .mk _ => 0 | .pointer => ⟨none, 16⟩)
