module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Common
import all Veir.Interpreter.Memory
import all Veir.Data.Pointer.Basic
import all Veir.ForLean
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Loads

/-! Instruction-selection validity proofs: Stores to indexed, constant-offset, and register addresses. -/

namespace Veir

open Puddle
open _root_.CTree

set_option warn.sorry false

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Llvm.interpretOp' GMIR.interpretOp'
  Builtin.interpretOpCTree Llvm.interpretOpCTree GMIR.interpretOpCTree

attribute [local implicit_reducible] TypeAttr

/-- No disjointness invariant on `MemoryState` is assumed by pattern validity. -/
private def storeCounterexampleMemory : MemoryState :=
  { bytes := {}, objects := #[⟨16, 8⟩, ⟨16, 0⟩] }

private theorem storeCounterexample_decode :
    storeCounterexampleMemory.decode 16 = ⟨1, 16⟩ := by
  simp [MemoryState.decode, MemoryState.objectOfAddress, storeCounterexampleMemory,
    List.range_succ, List.foldl]

/-- Erasing the pointer object and decoding its address can turn a successful store into UB.
The same collision applies to each width and address mode (with zero GEP offset). -/
theorem lowerStore_pointer_decode_counterexample :
    (∃ mem, storeCounterexampleMemory.llvmStore ⟨0, 16⟩ (.int 8 (.val 42)) = Interp.ok mem) ∧
    storeCounterexampleMemory.store (storeCounterexampleMemory.decode 16)
      (ByteArray.empty.push 42) = Interp.ub none := by
  constructor
  · simp [MemoryState.llvmStore, Data.Pointer.null, MemoryState.store,
      MemoryState.checkAccess, MemoryState.getObject?, MemoryObject.holds,
      storeCounterexampleMemory]
  · rw [storeCounterexample_decode]
    simp [MemoryState.store, MemoryState.checkAccess, MemoryState.getObject?,
      MemoryObject.holds, storeCounterexampleMemory]

/-- Checked witnesses for all twelve store statements, with their width matcher and
zero-offset address-mode hypotheses. Each LLVM store succeeds and the target store has UB. -/
theorem lowerStore_all_modes_counterexample (mode : AddrMode)
    (bytes : Nat) (hw : bytes ∈ [1, 2, 4, 8]) :
    memoryCounterexampleAddress mode ∧
    memAccessWidth? (TypeAttr.of IntegerType ⟨8 * bytes, .signless⟩) = some bytes ∧
    (∃ mem, storeCounterexampleMemory.llvmStore ⟨0, 16⟩
      (.int (8 * bytes) (.val 42)) = Interp.ok mem) ∧
    storeCounterexampleMemory.store (storeCounterexampleMemory.decode 16)
      ((42 : UInt64).toByteArrayLE.extract 0 bytes) = Interp.ub none := by
  refine ⟨memoryCounterexampleAddress_valid mode, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl <;>
      simp [memAccessWidth?, DataLayout.getTypeSize, DataLayout.riscv64,
        DataLayout.queryRISCV64, Attribute.of_def, -Attribute.integerType_eq_of] <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl <;>
      simp [MemoryState.llvmStore, Data.Pointer.null, MemoryState.store,
        MemoryState.checkAccess, MemoryState.getObject?, MemoryObject.holds,
        storeCounterexampleMemory, UInt16.toByteArrayLE, UInt32.toByteArrayLE,
        UInt64.toByteArrayLE] <;>
      exact ⟨_, rfl⟩
  · rw [storeCounterexample_decode]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl <;>
      simp [MemoryState.store, MemoryState.checkAccess, MemoryState.getObject?,
        MemoryObject.holds, storeCounterexampleMemory]

/- Blocked by pointer object erasure; see `lowerStore_all_modes_counterexample`. -/
theorem lowerStore_gepIndex_sb_valid :
    Puddle.CTree.Pattern.Valid (lowerStore .gepIndex 1 .sb) := by
  dsimp only [lowerStore, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  sorry

/- Blocked by pointer object erasure; see `lowerStore_all_modes_counterexample`. -/
theorem lowerStore_gepIndex_sh_valid :
    Puddle.CTree.Pattern.Valid (lowerStore .gepIndex 2 .sh) := by
  dsimp only [lowerStore, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

/- Blocked by pointer object erasure; see `lowerStore_all_modes_counterexample`. -/
theorem lowerStore_gepIndex_sw_valid :
    Puddle.CTree.Pattern.Valid (lowerStore .gepIndex 4 .sw) := by
  dsimp only [lowerStore, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

/- Blocked by pointer object erasure; see `lowerStore_all_modes_counterexample`. -/
theorem lowerStore_gepIndex_sd_valid :
    Puddle.CTree.Pattern.Valid (lowerStore .gepIndex 8 .sd) := by
  dsimp only [lowerStore, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

/- Blocked by pointer object erasure; see `lowerStore_all_modes_counterexample`. -/
theorem lowerStore_gepConst_sb_valid :
    Puddle.CTree.Pattern.Valid (lowerStore .gepConst 1 .sb) := by
  dsimp only [lowerStore, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

/- Blocked by pointer object erasure; see `lowerStore_all_modes_counterexample`. -/
theorem lowerStore_gepConst_sh_valid :
    Puddle.CTree.Pattern.Valid (lowerStore .gepConst 2 .sh) := by
  dsimp only [lowerStore, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

/- Blocked by pointer object erasure; see `lowerStore_all_modes_counterexample`. -/
theorem lowerStore_gepConst_sw_valid :
    Puddle.CTree.Pattern.Valid (lowerStore .gepConst 4 .sw) := by
  dsimp only [lowerStore, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

/- Blocked by pointer object erasure; see `lowerStore_all_modes_counterexample`. -/
theorem lowerStore_gepConst_sd_valid :
    Puddle.CTree.Pattern.Valid (lowerStore .gepConst 8 .sd) := by
  dsimp only [lowerStore, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

/- Blocked by pointer object erasure; see `lowerStore_all_modes_counterexample`. -/
theorem lowerStore_reg_sb_valid :
    Puddle.CTree.Pattern.Valid (lowerStore .reg 1 .sb) := by
  dsimp only [lowerStore, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

/- Blocked by pointer object erasure; see `lowerStore_all_modes_counterexample`. -/
theorem lowerStore_reg_sh_valid :
    Puddle.CTree.Pattern.Valid (lowerStore .reg 2 .sh) := by
  dsimp only [lowerStore, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

/- Blocked by pointer object erasure; see `lowerStore_all_modes_counterexample`. -/
theorem lowerStore_reg_sw_valid :
    Puddle.CTree.Pattern.Valid (lowerStore .reg 4 .sw) := by
  dsimp only [lowerStore, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

/- Blocked by pointer object erasure; see `lowerStore_all_modes_counterexample`. -/
theorem lowerStore_reg_sd_valid :
    Puddle.CTree.Pattern.Valid (lowerStore .reg 8 .sd) := by
  dsimp only [lowerStore, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

end Veir
