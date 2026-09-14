module

public import Veir.Interfaces.FoldInterfaces.Lemmas

import all Veir.Data.Refinement
import all Veir.IR.Attribute
import all Veir.Interpreter.Basic
import all Veir.GlobalOpInfo
import all Veir.Dialects.Arith.OpInfo
import all Veir.Dialects.LLVM.OpInfo
import all Veir.Dialects.RISCV.OpInfo
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.RISCV.Reg.Basic

/-!
# Proofs for dialect fold-table entries

Each theorem covers every successful lookup of its opcode, with arbitrary
known operands and properties. Signatures are stated directly, without an IR
context or assumptions about the folding driver. Integer widths are arbitrary.
-/

public section

namespace Veir
open Data

private theorem fold_add_zero (x : LLVM.Int w) (nsw nuw : Bool) :
    LLVM.Int.add x (.val (0#w)) nsw nuw = x := by
  cases x with
  | poison => rfl
  | val x =>
    simp [LLVM.Int.add, Id.run, BitVec.saddOverflow, BitVec.uaddOverflow,
      Nat.not_le.mpr x.isLt, Int.not_le.mpr (BitVec.toInt_lt (x := x)),
      Int.not_lt.mpr (BitVec.le_toInt x)]

private theorem overflow_zero (x : LLVM.Int w) :
    LLVM.Int.uaddOverflowFlag x (.val (0#w)) ⊒ .val (0#1) := by
  cases x with
  | poison => simp [LLVM.Int.uaddOverflowFlag, Id.run, isRefinedBy]
  | val x =>
    simp [LLVM.Int.uaddOverflowFlag, Id.run, BitVec.uaddOverflow,
      Nat.not_le.mpr x.isLt, isRefinedBy]

private theorem arith_addi_lookup
    (h : HasOpInfo.tryFold (OpCode.arith .addi) properties types known = some decisions) :
    ∃ lhs bw, known = #[lhs, some (.int bw (.val 0))] ∧
      decisions = #[.useOperand 0] := by
  change Arith.tryFold .addi properties types known = some decisions at h
  unfold Arith.tryFold at h
  repeat first | split at h | contradiction
  all_goals grind [Array.toList_inj]

private theorem arith_addui_extended_lookup
    (h : HasOpInfo.tryFold (OpCode.arith .addui_extended) properties types known = some decisions) :
    ∃ lhs bw, known = #[lhs, some (.int bw (.val 0))] ∧
      decisions = #[.useOperand 0, .useConstant (.int 1 (.val 0))] := by
  change Arith.tryFold .addui_extended properties types known = some decisions at h
  unfold Arith.tryFold at h
  repeat first | split at h | contradiction
  all_goals grind [Array.toList_inj]

private theorem llvm_add_lookup
    (h : HasOpInfo.tryFold (OpCode.llvm .add) properties types known = some decisions) :
    ∃ lhs bw, known = #[lhs, some (.int bw (.val 0))] ∧
      decisions = #[.useOperand 0] := by
  change Llvm.tryFold .add properties types known = some decisions at h
  unfold Llvm.tryFold at h
  repeat first | split at h | contradiction
  all_goals grind [Array.toList_inj]

private theorem riscv_andi_lookup
    (h : HasOpInfo.tryFold (OpCode.riscv .andi) properties types known = some decisions) :
    properties.value.value = 0 ∧ decisions = #[.useConstant (.reg ⟨0⟩)] := by
  change Riscv.tryFold .andi properties types known = some decisions at h
  unfold Riscv.tryFold at h
  repeat first | split at h | contradiction
  all_goals grind

/-- The arithmetic add-zero entry, including arbitrary overflow flags and poison inputs. -/
theorem Arith.tryFold_addi_correct (properties : Arith.propertiesOf .addi) (w : Nat) :
    FoldTable.CorrectAt (.arith .addi) properties
      #[(IntegerType.mk w : TypeAttr), (IntegerType.mk w : TypeAttr)]
      #[(IntegerType.mk w : TypeAttr)] := by
  apply FoldTable.correctAt_int_rhs (fun width => .val (0#width))
    (fun _ _ h => arith_addi_lookup h)
  · simp [FoldDecision.HasType]
  · intro lhs memory successors layout
    refine ⟨#[.int w lhs], ?_, ?_⟩
    · simp [FoldDecision.resolveAll, FoldDecision.resolve]
    · simp [Veir.interpretOp', Arith.interpretOp', LLVM.Int.cast_self, fold_add_zero,
        FoldTable.Refines]

/-- The extended-add entry refines both results, even when the unknown operand
is poison: its poison overflow flag may be replaced with concrete false. -/
theorem Arith.tryFold_addui_extended_correct (w : Nat) :
    FoldTable.CorrectAt (.arith .addui_extended) ()
      #[(IntegerType.mk w : TypeAttr), (IntegerType.mk w : TypeAttr)]
      #[(IntegerType.mk w : TypeAttr), (IntegerType.mk 1 : TypeAttr)] := by
  apply FoldTable.correctAt_int_rhs (fun width => .val (0#width))
    (fun _ _ h => arith_addui_extended_lookup h)
  · rw [FoldDecision.hasTypes_pair]; exact ⟨rfl, rfl⟩
  · intro lhs memory successors layout
    refine ⟨#[.int w lhs, .int 1 (.val 0)], ?_, ?_⟩
    · simp [FoldDecision.resolveAll, FoldDecision.resolve]
    · simp [Veir.interpretOp', Arith.interpretOp', LLVM.Int.cast_self, fold_add_zero,
        FoldTable.Refines, RuntimeValue.isRefinedBy, overflow_zero]

/-- LLVM add-zero is correct for every width and every choice of overflow flags. -/
theorem Llvm.tryFold_add_correct (properties : Llvm.propertiesOf .add) (w : Nat) :
    FoldTable.CorrectAt (.llvm .add) properties
      #[(IntegerType.mk w : TypeAttr), (IntegerType.mk w : TypeAttr)]
      #[(IntegerType.mk w : TypeAttr)] := by
  apply FoldTable.correctAt_int_rhs (fun width => .val (0#width))
    (fun _ _ h => llvm_add_lookup h)
  · simp [FoldDecision.HasType]
  · intro lhs memory successors layout
    refine ⟨#[.int w lhs], ?_, ?_⟩
    · simp [FoldDecision.resolveAll, FoldDecision.resolve]
    · simp [Veir.interpretOp', Llvm.interpretOp', LLVM.Int.cast_self, fold_add_zero,
        FoldTable.Refines]

/-- The RISC-V immediate-and-zero entry is correct for every register value.
The operand and result may have different register allocations. The successful
lookup itself establishes that the immediate is zero. -/
theorem Riscv.tryFold_andi_correct (properties : Riscv.propertiesOf .andi)
    (operandType resultType : RegisterType) :
    FoldTable.CorrectAt (.riscv .andi) properties
      #[(operandType : TypeAttr)] #[(resultType : TypeAttr)] := by
  intro known decisions _ hFold
  obtain ⟨hZero, rfl⟩ := riscv_andi_lookup hFold
  constructor
  · rw [FoldDecision.hasTypes_singleton]; trivial
  · intro operands hOperands _ memory successors layout
    obtain ⟨value, rfl⟩ := hOperands.reg_single
    refine ⟨#[.reg ⟨0⟩], ?_, ?_⟩
    · simp [FoldDecision.resolveAll, FoldDecision.resolve]
    · simp [Veir.interpretOp', Riscv.interpretOp', hZero, RISCV.andi, FoldTable.Refines]

end Veir
