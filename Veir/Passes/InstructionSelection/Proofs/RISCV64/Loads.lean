module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Common
import all Veir.Interpreter.Memory
import all Veir.Data.Pointer.Basic
import all Veir.Dialects.RISCV.OpInfo
import all Veir.Passes.InstructionSelection.RISCV64
import all Veir.Dialects.LLVM.OpInfo
import all Veir.Interfaces.DataLayoutInterfaces
import all Veir.DataLayout.RISCV64

/-! Instruction-selection validity proofs: Loads from indexed, constant-offset, and register addresses. -/

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
private def loadCounterexampleMemory : MemoryState :=
  { bytes := {}, objects := #[⟨16, 8⟩, ⟨16, 0⟩] }

private theorem loadCounterexample_decode :
    loadCounterexampleMemory.decode 16 = ⟨1, 16⟩ := by
  simp [MemoryState.decode, MemoryState.objectOfAddress, loadCounterexampleMemory,
    List.range_succ, List.foldl]

/-- Erasing the pointer object and decoding its address can turn a successful load into UB.
The same collision applies to each width and address mode (with zero GEP offset). -/
theorem lowerLoad_pointer_decode_counterexample :
    loadCounterexampleMemory.llvmLoad ⟨0, 16⟩
      (TypeAttr.of IntegerType ⟨8, .signless⟩) = Interp.ok (.int 8 .poison) ∧
    riscvLoad loadCounterexampleMemory 16 1 .signExt = Interp.ub none := by
  constructor
  · simp [MemoryState.llvmLoad, MemoryState.load, MemoryState.hasPoison,
      MemoryState.loadPoison, MemoryState.checkAccess, MemoryState.getObject?,
      MemoryObject.holds, loadCounterexampleMemory, Attribute.of_def, MemoryState.byte,
      MemoryByte.poisoned, Data.Pointer.null, -Attribute.integerType_eq_of]
    rfl
  · have h : loadCounterexampleMemory.load (loadCounterexampleMemory.decode 16) 1 =
        Interp.ub none := by
      rw [loadCounterexample_decode]
      simp [MemoryState.load, MemoryState.checkAccess, MemoryState.getObject?,
        MemoryObject.holds, loadCounterexampleMemory]
    simp [riscvLoad, h]

/-- Concrete well-typed zero-offset GEPs for both folded address modes. -/
def memoryCounterexampleGEP (dynamic : Bool) : GetelementptrProperties :=
  ⟨⟨⟨32, .signless⟩, #[if dynamic then -2147483648 else 0]⟩,
    TypeAttr.of IntegerType ⟨8, .signless⟩, ⟨0, ⟨32, .signless⟩⟩⟩

/-- The selected immediate is zero, and interpreting the GEP preserves the source pointer. -/
def memoryCounterexampleAddress (mode : AddrMode) : Prop :=
  match mode with
  | .reg => True
  | .gepConst =>
      selectAddrRegImm (memoryCounterexampleGEP false) #[] = some 0 ∧
      ∀ mem, Llvm.interpretOp' .getelementptr (memoryCounterexampleGEP false) #[]
        #[.addr (.val ⟨0, 16⟩)] #[] mem DataLayout.riscv64 =
        Interp.ok (#[.addr (.val ⟨0, 16⟩)], mem, none)
  | .gepIndex =>
      selectAddrRegImm (memoryCounterexampleGEP true) #[⟨⟨0, ⟨64, .signless⟩⟩⟩] = some 0 ∧
      ∀ mem, Llvm.interpretOp' .getelementptr (memoryCounterexampleGEP true) #[]
        #[.addr (.val ⟨0, 16⟩), .int 64 (.val 0)] #[] mem DataLayout.riscv64 =
        Interp.ok (#[.addr (.val ⟨0, 16⟩)], mem, none)

theorem memoryCounterexampleAddress_valid (mode : AddrMode) :
    memoryCounterexampleAddress mode := by
  cases mode <;>
    simp [memoryCounterexampleAddress, selectAddrRegImm, Llvm.interpretOp',
      memoryCounterexampleGEP, GEPIndex.decode, DataLayout.gepOffsets,
      DataLayout.getTypeAllocSize, DataLayout.riscv64, DataLayout.queryRISCV64,
      Attribute.of_def, -Attribute.integerType_eq_of, -Attribute.llvmArrayType_eq_of] <;>
    exact ⟨rfl, rfl⟩

private theorem loadCounterexample_integer_success (w : Nat) (hw : w ∈ [8, 16, 32, 64]) :
    loadCounterexampleMemory.llvmLoad ⟨0, 16⟩ (TypeAttr.of IntegerType ⟨w, .signless⟩) =
      Interp.ok (.int w .poison) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;>
    simp [MemoryState.llvmLoad, MemoryState.load, MemoryState.hasPoison,
      MemoryState.loadPoison, MemoryState.checkAccess, MemoryState.getObject?,
      MemoryObject.holds, loadCounterexampleMemory, Attribute.of_def, MemoryState.byte,
      MemoryByte.poisoned, Data.Pointer.null, -Attribute.integerType_eq_of] <;> rfl

private theorem loadCounterexample_riscv_ub (bytes : Nat) (hw : bytes ∈ [1, 2, 4, 8])
    (ext : LoadExtension) :
    riscvLoad loadCounterexampleMemory 16 bytes ext = Interp.ub none := by
  have h : loadCounterexampleMemory.load (loadCounterexampleMemory.decode 16) bytes.toUInt64 =
      Interp.ub none := by
    rw [loadCounterexample_decode]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl <;>
      simp [MemoryState.load, MemoryState.checkAccess, MemoryState.getObject?,
        MemoryObject.holds, loadCounterexampleMemory]
  simp [riscvLoad, h]

/-- Checked witnesses for all twelve integer-load statements: each of the three modes
and each of the four widths succeeds in LLVM and encounters UB in RISC-V. -/
theorem lowerLoad_integer_all_modes_counterexample (mode : AddrMode)
    (w : Nat) (hw : w ∈ [8, 16, 32, 64]) (ext : LoadExtension) :
    memoryCounterexampleAddress mode ∧
    loadCounterexampleMemory.llvmLoad ⟨0, 16⟩ (TypeAttr.of IntegerType ⟨w, .signless⟩) =
      Interp.ok (.int w .poison) ∧
    riscvLoad loadCounterexampleMemory 16 (w / 8) ext = Interp.ub none := by
  refine ⟨memoryCounterexampleAddress_valid mode,
    loadCounterexample_integer_success w hw, loadCounterexample_riscv_ub (w / 8) ?_ ext⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> simp

/-- Checked witnesses for the pointer-load statement in each of the three address modes. -/
theorem lowerLoad_pointer_all_modes_counterexample (mode : AddrMode) :
    memoryCounterexampleAddress mode ∧
    (∃ value, loadCounterexampleMemory.llvmLoad ⟨0, 16⟩
      (TypeAttr.of LLVM.PointerType ⟨0⟩) = Interp.ok value) ∧
    riscvLoad loadCounterexampleMemory 16 8 .zeroExt = Interp.ub none := by
  refine ⟨memoryCounterexampleAddress_valid mode, ?_,
    loadCounterexample_riscv_ub 8 (by simp) .zeroExt⟩
  simp [MemoryState.llvmLoad, MemoryState.loadByte, MemoryState.load, MemoryState.loadPoison,
    MemoryState.checkAccess, MemoryState.getObject?, MemoryObject.holds,
    loadCounterexampleMemory, Attribute.of_def, MemoryState.byte, MemoryByte.poisoned,
    Data.Pointer.null, -Attribute.llvmPointerType_eq_of]

/- Blocked by pointer object erasure; see `lowerLoad_integer_all_modes_counterexample` and
`lowerLoad_pointer_all_modes_counterexample`. -/
theorem lowerLoad_gepIndex_lb_valid :
    Puddle.CTree.Pattern.Valid (lowerLoad IntegerType .gepIndex (·.bitwidth = 8) .lb) := by
  dsimp only [lowerLoad, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  sorry

/- Blocked by pointer object erasure; see `lowerLoad_integer_all_modes_counterexample` and
`lowerLoad_pointer_all_modes_counterexample`. -/
theorem lowerLoad_gepIndex_lh_valid :
    Puddle.CTree.Pattern.Valid (lowerLoad IntegerType .gepIndex (·.bitwidth = 16) .lh) := by
  dsimp only [lowerLoad, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  sorry

/- Blocked by pointer object erasure; see `lowerLoad_integer_all_modes_counterexample` and
`lowerLoad_pointer_all_modes_counterexample`. -/
theorem lowerLoad_gepIndex_lw_valid :
    Puddle.CTree.Pattern.Valid (lowerLoad IntegerType .gepIndex (·.bitwidth = 32) .lw) := by
  dsimp only [lowerLoad, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  sorry

/- Blocked by pointer object erasure; see `lowerLoad_integer_all_modes_counterexample` and
`lowerLoad_pointer_all_modes_counterexample`. -/
theorem lowerLoad_gepIndex_ld_valid :
    Puddle.CTree.Pattern.Valid (lowerLoad IntegerType .gepIndex (·.bitwidth = 64) .ld) := by
  dsimp only [lowerLoad, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  sorry

/- Blocked by pointer object erasure; see `lowerLoad_integer_all_modes_counterexample` and
`lowerLoad_pointer_all_modes_counterexample`. -/
theorem lowerLoad_gepIndex_ptr_valid :
    Puddle.CTree.Pattern.Valid
      (lowerLoad LLVM.PointerType .gepIndex (fun _ => true) .ld) := by
  dsimp only [lowerLoad, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  sorry

/- Blocked by pointer object erasure; see `lowerLoad_integer_all_modes_counterexample` and
`lowerLoad_pointer_all_modes_counterexample`. -/
theorem lowerLoad_gepConst_lb_valid :
    Puddle.CTree.Pattern.Valid (lowerLoad IntegerType .gepConst (·.bitwidth = 8) .lb) := by
  dsimp only [lowerLoad, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  sorry

/- Blocked by pointer object erasure; see `lowerLoad_integer_all_modes_counterexample` and
`lowerLoad_pointer_all_modes_counterexample`. -/
theorem lowerLoad_gepConst_lh_valid :
    Puddle.CTree.Pattern.Valid (lowerLoad IntegerType .gepConst (·.bitwidth = 16) .lh) := by
  dsimp only [lowerLoad, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  sorry

/- Blocked by pointer object erasure; see `lowerLoad_integer_all_modes_counterexample` and
`lowerLoad_pointer_all_modes_counterexample`. -/
theorem lowerLoad_gepConst_lw_valid :
    Puddle.CTree.Pattern.Valid (lowerLoad IntegerType .gepConst (·.bitwidth = 32) .lw) := by
  dsimp only [lowerLoad, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  sorry

/- Blocked by pointer object erasure; see `lowerLoad_integer_all_modes_counterexample` and
`lowerLoad_pointer_all_modes_counterexample`. -/
theorem lowerLoad_gepConst_ld_valid :
    Puddle.CTree.Pattern.Valid (lowerLoad IntegerType .gepConst (·.bitwidth = 64) .ld) := by
  dsimp only [lowerLoad, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  sorry

/- Blocked by pointer object erasure; see `lowerLoad_integer_all_modes_counterexample` and
`lowerLoad_pointer_all_modes_counterexample`. -/
theorem lowerLoad_gepConst_ptr_valid :
    Puddle.CTree.Pattern.Valid
      (lowerLoad LLVM.PointerType .gepConst (fun _ => true) .ld) := by
  dsimp only [lowerLoad, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

/- Blocked by pointer object erasure; see `lowerLoad_integer_all_modes_counterexample` and
`lowerLoad_pointer_all_modes_counterexample`. -/
theorem lowerLoad_reg_lb_valid :
    Puddle.CTree.Pattern.Valid (lowerLoad IntegerType .reg (·.bitwidth = 8) .lb) := by
  dsimp only [lowerLoad, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

/- Blocked by pointer object erasure; see `lowerLoad_integer_all_modes_counterexample` and
`lowerLoad_pointer_all_modes_counterexample`. -/
theorem lowerLoad_reg_lh_valid :
    Puddle.CTree.Pattern.Valid (lowerLoad IntegerType .reg (·.bitwidth = 16) .lh) := by
  dsimp only [lowerLoad, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

/- Blocked by pointer object erasure; see `lowerLoad_integer_all_modes_counterexample` and
`lowerLoad_pointer_all_modes_counterexample`. -/
theorem lowerLoad_reg_lw_valid :
    Puddle.CTree.Pattern.Valid (lowerLoad IntegerType .reg (·.bitwidth = 32) .lw) := by
  dsimp only [lowerLoad, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

/- Blocked by pointer object erasure; see `lowerLoad_integer_all_modes_counterexample` and
`lowerLoad_pointer_all_modes_counterexample`. -/
theorem lowerLoad_reg_ld_valid :
    Puddle.CTree.Pattern.Valid (lowerLoad IntegerType .reg (·.bitwidth = 64) .ld) := by
  dsimp only [lowerLoad, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

/- Blocked by pointer object erasure; see `lowerLoad_integer_all_modes_counterexample` and
`lowerLoad_pointer_all_modes_counterexample`. -/
theorem lowerLoad_reg_ptr_valid :
    Puddle.CTree.Pattern.Valid
      (lowerLoad LLVM.PointerType .reg (fun _ => true) .ld) := by
  dsimp only [lowerLoad, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

end Veir
