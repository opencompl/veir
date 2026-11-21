module

public import Veir.Interpreter.Lemmas
import Veir.Interpreter.Refinement.Memory

import all Veir.Interpreter.Memory
import all Veir.Dialects.LLVM.OpInfo

public section

/-!
# Monotonicity of the LLVM interpreter

An LLVM opcode is monotone when refining its operands and its memory refines its result.
-/

open Veir.Data

namespace Veir

/--
`llvm.load` is monotone: a poison pointer is undefined behavior, and a load through a pointer
from refined memory gives a refined value.
-/
instance llvm_monotone_load : InterpretOp'Monotone (.llvm .load) where
  monotone properties resultTypes operands operands' blockOperands mem mem' h hMem := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · next x heq =>
      obtain ⟨x', hT, rfl | ⟨c, rfl, hc⟩⟩ := RuntimeValue.toList_addr1_of_isRefinedBy h heq
      · simp
      obtain ⟨c', rfl, hc'⟩ : ∃ c', x' = .val c' ∧ (c ⊒ c') := by
        rcases hc with rfl | rfl <;> simp
      simp only [hT, Pointer.checkAlignment_of_isRefinedBy hc']
      rcases resultTypes.toList with _ | ⟨type, _ | _⟩
      · simp [liftM]
      · refine Interp.isRefinedBy_bind_same fun _ => ?_
        exact Interp.isRefinedBy_bind (MemoryState.llvmLoad_isRefinedBy_of_refines hMem hc' type)
          fun v v' hv => by simpa using result_single hv hMem
      · simp [liftM]
    · simp [Interp.isRefinedBy]

end Veir

end
