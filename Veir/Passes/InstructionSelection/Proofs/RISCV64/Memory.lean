module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Common
import all Veir.Interpreter.Memory
import all Veir.Interpreter.Refinement.Basic
import all Veir.Data.LLVM.Ptr

/-! Instruction-selection validity proofs: Address materialization, lifetime, and memory intrinsics. -/

namespace Veir

open Puddle
open _root_.CTree

set_option warn.sorry false

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Llvm.interpretOp' GMIR.interpretOp'
  Builtin.interpretOpCTree Llvm.interpretOpCTree GMIR.interpretOpCTree

attribute [local implicit_reducible] TypeAttr

/-- The validity predicate quantifies over memory states without requiring disjoint objects. -/
private def addressofCounterexampleMemory : MemoryState :=
  { bytes := {}, objects := #[⟨16, 1⟩, ⟨16, 1⟩],
    globals := ({} : Std.HashMap String Nat).insert "@g" 0 }

/-- `la` followed by pointer reconstruction loses the global's object identity. -/
theorem addressof_pointer_roundtrip_counterexample :
    addressofCounterexampleMemory.pointerToGlobal "@g" = some ⟨0, 16⟩ ∧
    addressofCounterexampleMemory.decode 16 = ⟨1, 16⟩ ∧
    ¬ (RuntimeValue.addr (.val ⟨0, 16⟩) ⊒ RuntimeValue.addr (.val ⟨1, 16⟩)) := by
  constructor
  · simp [MemoryState.pointerToGlobal, addressofCounterexampleMemory]
  constructor
  · simp [MemoryState.decode, MemoryState.objectOfAddress, addressofCounterexampleMemory,
      List.range_succ, List.foldl]
  · simp [RuntimeValue.isRefinedBy, Data.LLVM.Ptr.isRefinedBy]

/-- The reconstructed pointer in `addressof_pointer_roundtrip_counterexample`
fails the actual CTree return-value simulation obligation. -/
theorem addressof_pointer_simulation_counterexample :
    ¬ CTree.Sim
      (fun (target source : Array RuntimeValue × MemoryState × Option ControlFlowAction) =>
        OperationResult.isRefinedBy source target)
      (pure (#[.addr (.val ⟨1, 16⟩)], addressofCounterexampleMemory, none) : Tree _)
      (pure (#[.addr (.val ⟨0, 16⟩)], addressofCounterexampleMemory, none) : Tree _) := by
  simp [OperationResult.isRefinedBy, RuntimeValue.arrayIsRefinedBy,
    RuntimeValue.isRefinedBy, Data.LLVM.Ptr.isRefinedBy]

/-- A zero-length memcpy succeeds even in empty memory, while the emitted call fails. -/
theorem memcpyCall_semantics_counterexample :
    Llvm.interpretOp' .intr__memcpy (default : LLVMMemIntrinsicProperties) #[]
      #[.addr (.val ⟨0, 0⟩), .addr (.val ⟨0, 0⟩), .int 64 (.val 0)] #[]
      MemoryState.empty DataLayout.riscv64 = Interp.ok (#[], MemoryState.empty, none) ∧
    Riscv_Cf.interpretOp' .call ⟨some ⟨"@memcpy"⟩⟩ #[]
      #[.reg ⟨0⟩, .reg ⟨0⟩, .reg ⟨0⟩] #[] = Interp.fail none := by
  constructor
  · rfl
  · rfl

/-- A zero-length memset succeeds even in empty memory, while the emitted call fails. -/
theorem memsetCall_semantics_counterexample :
    Llvm.interpretOp' .intr__memset (default : LLVMMemIntrinsicProperties) #[]
      #[.addr (.val ⟨0, 0⟩), .int 8 (.val 0), .int 64 (.val 0)] #[]
      MemoryState.empty DataLayout.riscv64 = Interp.ok (#[], MemoryState.empty, none) ∧
    Riscv_Cf.interpretOp' .call ⟨some ⟨"@memset"⟩⟩ #[]
      #[.reg ⟨0⟩, .reg ⟨0⟩, .reg ⟨0⟩] #[] = Interp.fail none := by
  constructor
  · rfl
  · rfl

theorem lifetimeStart_valid :
    Puddle.CTree.Pattern.Valid (lowerLifetime .intr__lifetime__start) := by
  dsimp only [lowerLifetime]
  simpPuddleValid
  simp [ctree_semantics]

theorem lifetimeEnd_valid :
    Puddle.CTree.Pattern.Valid (lowerLifetime .intr__lifetime__end) := by
  dsimp only [lowerLifetime]
  simpPuddleValid
  simp [ctree_semantics]

/- Blocked by `addressof_pointer_roundtrip_counterexample`: object identity is not preserved. -/
theorem addressof_pattern_valid :
    Puddle.CTree.Pattern.Valid addressof_pattern := by
  unfold addressof_pattern
  simpPuddleValid
  simp [ctree_semantics]
  sorry

/- Blocked by `memcpyCall_semantics_counterexample`: calls have no local semantics. -/
theorem memcpyCall_valid :
    Puddle.CTree.Pattern.Valid (memIntrinsicCallPattern false) := by
  dsimp only [memIntrinsicCallPattern]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

/- Blocked by `memsetCall_semantics_counterexample`: calls have no local semantics. -/
theorem memsetCall_valid :
    Puddle.CTree.Pattern.Valid (memIntrinsicCallPattern true) := by
  dsimp only [memIntrinsicCallPattern]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

end Veir
