module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.MemoryLemmas
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.MemoryAddressLemmas

namespace Veir

open Puddle
open _root_.CTree

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Llvm.interpretOp' GMIR.interpretOp'
  Builtin.interpretOpCTree Llvm.interpretOpCTree GMIR.interpretOpCTree
attribute [local implicit_reducible] TypeAttr

def StoreValueRefines (value : RuntimeValue) (reg : Data.RISCV.Reg) : Prop :=
  match value with
  | .int w x => x ⊒ Data.LLVM.Int.val (reg.val.setWidth w)
  | .addr p => p ⊒ Data.LLVM.Ptr.val ⟨UInt64.ofBitVec reg.val⟩
  | _ => False

def StorePrimitiveRefines (n : Nat) : Prop :=
  ∀ (memory : MemoryState) (p : Data.Pointer) (ty : TypeAttr)
    (value : RuntimeValue) (reg : Data.RISCV.Reg),
    memAccessWidth? ty = some n → value.Conforms ty → StoreValueRefines value reg →
    Interp.isRefinedBy MemoryState.isRefinedBy
      (memory.llvmStore p value)
      (memory.store p ((UInt64.ofBitVec reg.val).toByteArrayLE.extract 0 n))

/-- Normalize a full-width store, including its dependent default poison mask. -/
theorem store_fullWidth (memory : MemoryState) (p : Data.Pointer) (u : UInt64) :
    memory.store p (u.toByteArrayLE.extract 0 8) = memory.store p u.toByteArrayLE := by
  have he : u.toByteArrayLE.extract 0 8 = u.toByteArrayLE := by
    rw [←UInt64.toByteArrayLE_size u, ByteArray.extract_zero_size]
  exact congrArg (fun data : ByteArray => memory.store p data) he

/-- A successful source store is simulated by a raw store with refined memory. -/
theorem rawStore_sim (memory source : MemoryState) (p : Data.Pointer) (data : ByteArray)
    (href : Interp.isRefinedBy MemoryState.isRefinedBy (.ok source) (memory.store p data)) :
    CTree.Sim (fun target source => OperationResult.isRefinedBy source target)
      (CTree.bind
        (monadLift (do
          let mem ← memory.store p data
          pure ((#[] : Array RuntimeValue), mem, (none : Option ControlFlowAction))))
        (fun result => pure (#[], result.2.1, none)) : Tree _)
      (pure (#[], source, none) : Tree _) := by
  cases h : memory.store p data <;> rw [h] at href
  all_goals simp only [Interp.isRefinedBy] at href
  all_goals simp [h, ctree_semantics, href]

end Veir
