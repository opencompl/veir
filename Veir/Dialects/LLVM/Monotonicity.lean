module

import all Veir.Dialects.LLVM.OpInfo
import all Veir.Interpreter.Basic
import all Veir.Data.Refinement
public import Veir.Interpreter.Lemmas

public section

/-!
# Monotonicity of the LLVM interpreter

An LLVM opcode is monotone in its operands when a more defined operand cannot change what it
does. That holds for the opcodes that only read their operands, and fails for `freeze`, which
turns poison into zero, and for `store`, which writes a poison byte where a refined operand
writes a concrete one and so leaves a different memory.
-/

namespace Veir

/--
A load reads through its pointer operand. A poison pointer is undefined behaviour and a
concrete one is fixed by refinement, so both sides read the same address.
-/
instance : InterpretOp'Monotone (.llvm .load) where
  monotone props resultTypes operands operands' blockOperands mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · split
      · next ptr hOps =>
        obtain ⟨w, hw, hRef⟩ := RuntimeValue.arrayIsRefinedBy_toList_singleton hOps h
        obtain rfl : w = .addr (.val ptr) := by
          grind [RuntimeValue.isRefinedBy, Data.LLVM.Ptr.isRefinedBy,
            cases RuntimeValue, cases Data.LLVM.Ptr]
        rw [hw]
        exact Interp.isRefinedBy_refl_operationResult _
      · simp [Interp.isRefinedBy]
    · simp [Interp.isRefinedBy]

end Veir

end
