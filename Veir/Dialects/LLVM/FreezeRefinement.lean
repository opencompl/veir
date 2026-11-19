module

public import Veir.Dialects.LLVM.Interpreter
import all Veir.Dialects.LLVM.Interpreter
import all Veir.Dialects.LLVM.OpInfo
public import Veir.Interpreter.Refinement.Lemmas
import all Veir.Data.LLVM.Ptr.Basic

public section

namespace Veir.Llvm

open Veir.Data
open _root_.CTree
open Veir.CTree

/-- Freezing a concrete pointer preserves its address. -/
theorem freeze_concrete_pointer (p : Pointer) (memory : MemoryState) :
    interpretOpCTree (E := ErrorE ⊕ₑ UBE) .freeze () #[]
      #[.addr (.val p)] #[] memory = pure (#[.addr (.val p)], memory, none) := by
  rfl

/-- Freezing poison admits every concrete pointer address. -/
theorem freeze_poison_pointer_allows (p : Pointer) (memory : MemoryState) :
    Sim (fun target source => OperationResult.isRefinedBy source target)
      (pure (#[.addr (.val p)], memory, none) : Tree _)
      (interpretOpCTree .freeze () #[] #[.addr .poison] #[] memory) := by
  simp only [interpretOpCTree, _root_.CTree.CTree.choose_def,
    _root_.CTree.CTree.tau_def, _root_.CTree.bind_tau]
  apply (Sim.pure_tau _ _ _ _).mpr
  refine ⟨p.address.toBitVec, ?_⟩
  simp [OperationResult.isRefinedBy, RuntimeValue.arrayIsRefinedBy,
    RuntimeValue.isRefinedBy, LLVM.Ptr.isRefinedBy]

/-- Pointer freeze is monotone for every pair of refining pointer operands. -/
theorem freeze_pointer_monotone (source target : LLVM.Ptr)
    (h : source ⊒ target) (memory : MemoryState) :
    Sim (fun target source => OperationResult.isRefinedBy source target)
      (interpretOpCTree (E := ErrorE ⊕ₑ UBE) .freeze () #[]
        #[.addr target] #[] memory)
      (interpretOpCTree .freeze () #[] #[.addr source] #[] memory) := by
  cases source with
  | val p =>
    cases target <;> simp_all [freeze_concrete_pointer, Sim.pure,
      OperationResult.isRefinedBy, RuntimeValue.arrayIsRefinedBy, RuntimeValue.isRefinedBy]
  | poison =>
    cases target with
    | val p => exact freeze_poison_pointer_allows p memory
    | poison =>
      apply Sim.refl
      intro result
      exact OperationResult.isRefinedBy_refl result

end Veir.Llvm
