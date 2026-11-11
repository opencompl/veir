module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.MemoryLemmas
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.MemoryAddressLemmas

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.StoreValueLemmas

namespace Veir

open Puddle
open _root_.CTree

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Llvm.interpretOp' GMIR.interpretOp'
  Builtin.interpretOpCTree Llvm.interpretOpCTree GMIR.interpretOpCTree
attribute [local implicit_reducible] TypeAttr

theorem lowerStore_reg_sb_of (store_refines : StorePrimitiveRefines 1) :
    Puddle.CTree.Pattern.Valid (lowerStore .reg 1 .sb) := by
  dsimp only [lowerStore, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  intro ty width value conforms argType arg harg props verified memory
  have types := memAccessWidth_cases width
  rcases types with (⟨sign, rfl⟩ | ⟨pointer, rfl, wrong⟩)
  · simp only [RuntimeValue.Conforms.integerType] at conforms
    obtain ⟨x, rfl⟩ := conforms
    cases arg <;> simp [ctree_semantics]
    rename_i pointer
    cases pointer with
    | poison => simp
    | val p =>
      simp only [Data.LLVM.Ptr.toInt, RuntimeValue.storedType]
      cases ha : p.checkAlignment (Llvm.accessAlignment DataLayout.riscv64 props.alignment
          (Attribute.of IntegerType (IntegerType.signless 8))) <;> simp [ha, ctree_semantics]
      cases hs : memory.llvmStore p (.int 8 x) <;> simp [hs, ctree_semantics]
      intro ra hra rv hrv
      have href := store_refines memory p (TypeAttr.of IntegerType ⟨8, sign⟩) (.int 8 x) rv width
        (by simp) (by cases x <;> simp_all [StoreValueRefines, isRefinedBy])
      rw [hs] at href
      simpa [hra, riscvEffectiveAddr, RISCVMemProperties.imm12, MemoryState.decode,
        OperationResult.isRefinedBy] using
        rawStore_sim memory _ p ((UInt64.ofBitVec rv.val).toByteArrayLE.extract 0 1) href
  · contradiction

theorem lowerStore_reg_sh_of (store_refines : StorePrimitiveRefines 2) :
    Puddle.CTree.Pattern.Valid (lowerStore .reg 2 .sh) := by
  dsimp only [lowerStore, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  intro ty width value conforms argType arg harg props verified memory
  have types := memAccessWidth_cases width
  rcases types with (⟨sign, rfl⟩ | ⟨pointer, rfl, wrong⟩)
  · simp only [RuntimeValue.Conforms.integerType] at conforms
    obtain ⟨x, rfl⟩ := conforms
    cases arg <;> simp [ctree_semantics]
    rename_i pointer
    cases pointer with
    | poison => simp
    | val p =>
      simp only [Data.LLVM.Ptr.toInt, RuntimeValue.storedType]
      cases ha : p.checkAlignment (Llvm.accessAlignment DataLayout.riscv64 props.alignment
          (Attribute.of IntegerType (IntegerType.signless 16))) <;> simp [ha, ctree_semantics]
      cases hs : memory.llvmStore p (.int 16 x) <;> simp [hs, ctree_semantics]
      intro ra hra rv hrv
      have href := store_refines memory p (TypeAttr.of IntegerType ⟨16, sign⟩) (.int 16 x) rv width
        (by simp) (by cases x <;> simp_all [StoreValueRefines, isRefinedBy])
      rw [hs] at href
      simpa [hra, riscvEffectiveAddr, RISCVMemProperties.imm12, MemoryState.decode,
        OperationResult.isRefinedBy] using
        rawStore_sim memory _ p ((UInt64.ofBitVec rv.val).toByteArrayLE.extract 0 2) href
  · contradiction

theorem lowerStore_reg_sw_of (store_refines : StorePrimitiveRefines 4) :
    Puddle.CTree.Pattern.Valid (lowerStore .reg 4 .sw) := by
  dsimp only [lowerStore, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  intro ty width value conforms argType arg harg props verified memory
  have types := memAccessWidth_cases width
  rcases types with (⟨sign, rfl⟩ | ⟨pointer, rfl, wrong⟩)
  · simp only [RuntimeValue.Conforms.integerType] at conforms
    obtain ⟨x, rfl⟩ := conforms
    cases arg <;> simp [ctree_semantics]
    rename_i pointer
    cases pointer with
    | poison => simp
    | val p =>
      simp only [Data.LLVM.Ptr.toInt, RuntimeValue.storedType]
      cases ha : p.checkAlignment (Llvm.accessAlignment DataLayout.riscv64 props.alignment
          (Attribute.of IntegerType (IntegerType.signless 32))) <;> simp [ha, ctree_semantics]
      cases hs : memory.llvmStore p (.int 32 x) <;> simp [hs, ctree_semantics]
      intro ra hra rv hrv
      have href := store_refines memory p (TypeAttr.of IntegerType ⟨32, sign⟩) (.int 32 x) rv width
        (by simp) (by cases x <;> simp_all [StoreValueRefines, isRefinedBy])
      rw [hs] at href
      simpa [hra, riscvEffectiveAddr, RISCVMemProperties.imm12, MemoryState.decode,
        OperationResult.isRefinedBy] using
        rawStore_sim memory _ p ((UInt64.ofBitVec rv.val).toByteArrayLE.extract 0 4) href
  · contradiction

set_option maxHeartbeats 800000 in
theorem lowerStore_reg_sd_of (store_refines : StorePrimitiveRefines 8) :
    Puddle.CTree.Pattern.Valid (lowerStore .reg 8 .sd) := by
  dsimp only [lowerStore, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  intro ty width value conforms argType arg harg props verified memory
  have types := memAccessWidth_cases width
  rcases types with (⟨sign, rfl⟩ | ⟨pointer, rfl, wrong⟩)
  · simp only [RuntimeValue.Conforms.integerType] at conforms
    obtain ⟨x, rfl⟩ := conforms
    cases arg <;> simp [ctree_semantics]
    rename_i pointer
    cases pointer with
    | poison => simp
    | val p =>
      simp only [Data.LLVM.Ptr.toInt, RuntimeValue.storedType]
      cases ha : p.checkAlignment (Llvm.accessAlignment DataLayout.riscv64 props.alignment
          (Attribute.of IntegerType (IntegerType.signless 64))) <;> simp [ha, ctree_semantics]
      cases hs : memory.llvmStore p (.int 64 x) <;> simp [hs, ctree_semantics]
      intro ra hra rv hrv
      have href := store_refines memory p (TypeAttr.of IntegerType ⟨64, sign⟩) (.int 64 x) rv width
        (by simp) (by cases x <;> simp_all [StoreValueRefines, isRefinedBy])
      rw [hs] at href
      rw [store_fullWidth] at href
      simpa [hra, riscvEffectiveAddr, RISCVMemProperties.imm12, MemoryState.decode,
        OperationResult.isRefinedBy] using
        rawStore_sim memory _ p (UInt64.ofBitVec rv.val).toByteArrayLE href
  · simp only [RuntimeValue.Conforms.llvmPointerType] at conforms
    obtain ⟨x, rfl⟩ := conforms
    cases arg <;> simp [ctree_semantics]
    rename_i base
    cases base with
    | poison => simp
    | val p =>
      simp only [Data.LLVM.Ptr.toInt, RuntimeValue.storedType]
      cases ha : p.checkAlignment (Llvm.accessAlignment DataLayout.riscv64 props.alignment
          (Attribute.of LLVM.PointerType LLVM.PointerType.mk)) <;> simp [ha, ctree_semantics]
      cases hs : memory.llvmStore p (.addr x) <;> simp [hs, ctree_semantics]
      intro ra hra rv hrv
      have href := store_refines memory p (TypeAttr.of LLVM.PointerType pointer) (.addr x) rv width
        (by simp) (by cases x <;> simp_all [StoreValueRefines, Data.LLVM.Ptr.isRefinedBy,
          Data.Pointer.isRefinedBy, Data.LLVM.Ptr.toInt])
      rw [hs] at href
      rw [store_fullWidth] at href
      simpa [hra, riscvEffectiveAddr, RISCVMemProperties.imm12, MemoryState.decode,
        OperationResult.isRefinedBy] using
        rawStore_sim memory _ p (UInt64.ofBitVec rv.val).toByteArrayLE href

end Veir
