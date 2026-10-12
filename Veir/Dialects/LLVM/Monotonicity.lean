module

public import Veir.Interpreter.Lemmas

public section

/-!
# Monotonicity of the LLVM interpreter

An LLVM opcode is monotone in its operands when refining its operands refines its result.
-/

namespace Veir

/--
A load is monotone: a poison pointer is undefined behavior and
a concrete one is fixed by refinement.
-/
instance : InterpretOp'Monotone (.llvm .load) where
  monotone props resultTypes operands operands' blockOperands es h := by
    simp only [interpretOp']
    refine Interp.isRefinedBy_operationResult_withMemory es ?_
    simp only [Llvm.interpretOp']
    split
    · split
      · next ptr hOps =>
        obtain rfl : operands = #[.addr (.val ptr)] := List.eq_toArray_iff.mpr hOps
        obtain ⟨w, rfl, hRef⟩ := RuntimeValue.singleton_isRefinedBy_iff.mp h
        obtain rfl := RuntimeValue.addr_val_isRefinedBy_iff.mp hRef
        exact Interp.isRefinedBy_refl_operationResult _
      · simp [Interp.isRefinedBy]
    · simp [Interp.isRefinedBy]

end Veir

end
