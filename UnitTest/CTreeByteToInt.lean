import Veir.Dialects.Builtin.Interpreter
import Veir.Interpreter.CTreeRunner

/-!
  In CTrees, casting a partly poisoned byte to an integer nondeterministically chooses the bits
  that are poison. The runner's choice handler resolves these to zero (by default) or any other
  value.
-/

open Veir

/-- Casting a byte with the value 5 in its low four bits and poison in its high four bits. -/
private def castPartlyPoisonedByte : Tree (Data.LLVM.Int 8) :=
  Builtin.byteToIntCTree ⟨0x05#8, 0xF0#8, by decide⟩

/-- The result of a run. -/
private def result : Interp (Data.LLVM.Int 8) → String
  | .ok i => toString i
  | _ => "no result"

-- By default, the runner chooses zero bits.
/-- info: "0x05#8" -/
#guard_msgs in
#eval result castPartlyPoisonedByte.run

-- Any other bits may be chosen too, here all ones.
/-- info: "0xf5#8" -/
#guard_msgs in
#eval result (castPartlyPoisonedByte.run fun c => BitVec.allOnes c.bw)
