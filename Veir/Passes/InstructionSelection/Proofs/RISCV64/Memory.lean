module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Common
import all Veir.Dialects.RISCV.Interpreter
import all Veir.Interpreter.Memory
import all Veir.Interpreter.Refinement.Basic
import all Veir.Data.LLVM.Ptr
import all Veir.Data.LLVM.Ptr.Basic
import all Veir.Data.Pointer.Basic
import all Veir.Data.Casting

/-! Instruction-selection validity proofs: Address materialization, lifetime, and memory intrinsics. -/

namespace Veir

open Puddle
open _root_.CTree


attribute [local ctree_semantics]
  Riscv.interpretOpCTree
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Llvm.interpretOp' GMIR.interpretOp'
  Builtin.interpretOpCTree Llvm.interpretOpCTree GMIR.interpretOpCTree

attribute [local implicit_reducible] TypeAttr

/-- A zero-length memcpy succeeds even in empty memory, while the emitted call fails. -/
theorem memcpyCall_semantics_counterexample :
    Llvm.interpretOp' .intr__memcpy (default : LLVMMemIntrinsicProperties) #[]
      #[.addr (.val ⟨0⟩), .addr (.val ⟨0⟩), .int 64 (.val 0)] #[]
      MemoryState.empty DataLayout.riscv64 = Interp.ok (#[], MemoryState.empty, none) ∧
    Riscv_Cf.interpretOp' .call ⟨some ⟨"@memcpy"⟩⟩ #[]
      #[.reg ⟨0⟩, .reg ⟨0⟩, .reg ⟨0⟩] #[] = Interp.fail none := by
  constructor
  · rfl
  · rfl

/-- A zero-length memset succeeds even in empty memory, while the emitted call fails. -/
theorem memsetCall_semantics_counterexample :
    Llvm.interpretOp' .intr__memset (default : LLVMMemIntrinsicProperties) #[]
      #[.addr (.val ⟨0⟩), .int 8 (.val 0), .int 64 (.val 0)] #[]
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

theorem addressof_pattern_valid :
    Puddle.CTree.Pattern.Valid addressof_pattern := by
  unfold addressof_pattern
  simpPuddleValid
  simp [ctree_semantics]
  intro ty props verified
  obtain ⟨p, rfl⟩ := verified.llvm_addressof_result_type
  intro _ memory
  cases hglobal : memory.pointerToGlobal props.global_name.value with
  | none => simp
  | some pointer =>
    rcases pointer with ⟨address⟩
    simp [ctree_semantics, Builtin.interpretUnrealizedConversionCastCTree,
      Attribute.of_def, -Attribute.llvmPointerType_eq_of, MemoryState.ptrFromInt,
      MemoryState.decode, Data.LLVM.Ptr.toInt, LLVM.Int.toReg,
      RISCV.Reg.toInt, MemoryState.isRefinedBy_refl]

/- No validity theorem is exported for the call fallbacks: the checked
`memcpyCall_semantics_counterexample` and `memsetCall_semantics_counterexample`
above show that the emitted calls have no local interpreter semantics. -/

end Veir
