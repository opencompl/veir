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
a concrete one is refined only by itself or its wildcard.
-/
instance : InterpretOp'Monotone (.llvm .load) where
  monotone props resultTypes operands operands' blockOperands mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · split
      · next ptr hOps =>
        obtain rfl : operands = #[.addr (.val ptr)] := List.eq_toArray_iff.mpr hOps
        obtain ⟨w, rfl, hRef⟩ := RuntimeValue.singleton_isRefinedBy_iff.mp h
        rcases RuntimeValue.addr_val_isRefinedBy_iff.mp hRef with rfl | rfl
        · exact Interp.isRefinedBy_refl_operationResult _
        simp only [Data.Pointer.checkAlignment_wildcard]
        refine Interp.isRefinedBy_trans_eq (Interp.isRefinedBy_refl_operationResult _) ?_
        split
        · exact Interp.isRefinedBy_eq_bind_right _ fun _ =>
            Interp.isRefinedBy_eq_bind_left
              (Interp.isRefinedBy_eq_of_ok fun _ => MemoryState.llvmLoad_wildcard_of_ok) _
        · exact Interp.isRefinedBy_eq_refl _
      · simp [Interp.isRefinedBy]
    · simp [Interp.isRefinedBy]

end Veir

end
