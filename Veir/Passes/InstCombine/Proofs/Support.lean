module
import all Veir.Passes.InstCombine.InstructionSimplify
import Veir.Dialects.LLVM.VerifierLemmas
import all Veir.IR.Attribute
import all Veir.GlobalOpInfo
import all Veir.IR.OpCode
import all Veir.Interpreter.CTreeInterpreter
import all Veir.Dialects.LLVM.Interpreter
import all Veir.Dialects.LLVM.Properties
import all Veir.Dialects.LLVM.OpInfo
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.LLVM.Ptr.Basic
import Veir.PatternRewriter.Puddle.CTreeValidityTactics

namespace Veir.InstructionSimplify.CTreeProofs

open Puddle
open _root_.CTree

set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/- Generate the bit-blaster's signedness encoding once, so separately built proof
modules share its auxiliary declarations. -/
private theorem signedness_cases (s : IntegerType.Signedness) :
    s = .signless ∨ s = .signed ∨ s = .unsigned := by
  bv_decide

/-! Shared normalization for the InstructionSimplify validity proofs.

The verifier lemmas connect captured integer attributes to their declared result
widths. The CTree normalization retains poison, overflow flags, and all matcher
guards. Bitvector proof steps are supplied separately by each rule family.
-/

private theorem default_or_disjoint :
    (@default (propertiesOf (OpCode.llvm .or))
      (@instInhabitedPropertiesOf OpCode instIsOpCodeOpCode (.llvm .or))).disjoint = false := rfl

macro "normalizeInstructionSimplify" : tactic => `(tactic| (
  simpPuddleValid
  simp [puddle, OperationResult.isRefinedBy, Veir.CTree.interpretOp',
    Llvm.interpretOpCTree, Llvm.interpretOp', CTree.CanInterpretTo,
    RuntimeValue.isRefinedBy, default_or_disjoint]))

macro "proveBitReverse" : tactic => `(tactic| (
  normalizeInstructionSimplify
  intros
  veir_bv_normalize
  simp only [implies_true, and_true, true_and]
  intros
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_reverse, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_xor,
    BitVec.getMsbD_reverse, BitVec.getMsbD_and, BitVec.getMsbD_or, BitVec.getMsbD_xor] <;> bv_decide))

private theorem default_sub_properties :
    (@default (propertiesOf (OpCode.llvm .sub))
      (@instInhabitedPropertiesOf OpCode instIsOpCodeOpCode (.llvm .sub))) =
        { nsw := false, nuw := false } := rfl

theorem forall_constantIs {k : Int} {P : propertiesOf (OpCode.llvm .mlir__constant) → Prop} :
    (∀ p, constantIs k p = true → P p) ↔
      ∀ a, BitVec.ofInt a.type.bitwidth a.value = BitVec.ofInt a.type.bitwidth k →
        P { value := .integer a } := by
  constructor
  · intro h a ha; apply h; simpa [constantIs] using ha
  · intro h p hp
    rcases p with ⟨v⟩
    cases v <;> simp_all [constantIs]

theorem normalize_integer_constant_bits {w : Nat} (t : IntegerType) (v : Int) (h : t.bitwidth = w) :
    BitVec.ofInt w (IntegerAttr.ofInt v t).value = BitVec.ofInt w v := by
  subst w
  simp only [IntegerAttr.ofInt, IntegerAttr.normalizeValue]
  split <;> simp only [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.ofInt_toInt, BitVec.setWidth_eq]

private theorem bswap_other {w : Nat} (h16 : w ≠ 16) (h32 : w ≠ 32) (h64 : w ≠ 64)
    (x : Data.LLVM.Int w) : x.bswap = x := by
  cases x <;> simp [Data.LLVM.Int.bswap, h16, h32, h64, Id.run, pure]

macro "proveByteSwap" : tactic => `(tactic| (
  normalizeInstructionSimplify
  intro t ht
  obtain ⟨w, signedness⟩ := t
  by_cases h16 : w = 16
  · subst w; intros; veir_bv_decide
  by_cases h32 : w = 32
  · subst w; intros; veir_bv_decide
  by_cases h64 : w = 64
  · subst w; intros; veir_bv_decide
  intros
  simp only [bswap_other h16 h32 h64]
  veir_bv_normalize
  simp only [implies_true, and_true, true_and] <;> intros <;>
    first
    | assumption
    | rfl
    | (apply BitVec.eq_of_getLsbD_eq
       intro i hi
       simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_xor] <;> bv_decide)
    | grind))

macro "proveUnsignedAddDist" : tactic => `(tactic| (
  normalizeInstructionSimplify
  intros
  veir_bv_normalize
  simp_all only [Bool.and_eq_true, true_and, and_true, not_false_eq_true, implies_true,
    BitVec.saddOverflow_comm, BitVec.uaddOverflow_comm, BitVec.add_comm]
  constructor
  · split <;> grind
  · intros
    simp only [BitVec.ule, BitVec.toNat_add, BitVec.uaddOverflow] at *
    split <;> split <;> simp_all
    all_goals simp (disch := omega) only [Nat.mod_eq_of_lt] at * <;>
      (first | omega | (apply BitVec.eq_of_toNat_eq; simp -failIfUnchanged (disch := omega) only [BitVec.toNat_add, Nat.mod_eq_of_lt]; omega))))

macro "proveSignedAddDist" : tactic => `(tactic| (
  normalizeInstructionSimplify
  intros
  veir_bv_normalize
  simp_all only [Bool.and_eq_true, true_and, and_true, not_false_eq_true, implies_true,
    BitVec.saddOverflow_comm, BitVec.uaddOverflow_comm, BitVec.add_comm]
  constructor
  · split <;> grind
  · intros
    simp only [BitVec.sle] at *
    split <;> split <;> simp_all [-BitVec.toInt_add]
    all_goals simp -failIfUnchanged (disch := omega) only [BitVec.toInt_add_of_not_saddOverflow] at * <;>
      (first | omega | (apply BitVec.eq_of_toInt_eq; grind [BitVec.toInt_add_of_not_saddOverflow, BitVec.add_comm]))))

theorem forall_isIntegerConstant {P : LLVMConstantProperties → Prop} :
    (∀ p, isIntegerConstant p = true → P p) ↔
      ∀ a, True → P { value := .integer a } := by
  constructor
  · intro h a _; apply h; rfl
  · intro h p hp
    rcases p with ⟨v⟩
    cases v <;> simp_all [isIntegerConstant]

private theorem bitwidth_of_integer (t : IntegerType) :
    bitwidth (.of IntegerType t) = t.bitwidth := rfl

macro "normalizeConstantRule" : tactic => `(tactic| (
  simpPuddleValid
  simp [puddle, RuntimeValue.Conforms.integerType]
  repeat' first
    | erw [forall_constantIs]
    | erw [forall_isIntegerConstant]
    | erw [forall_verified_integer_constant]
    | intro
  simp_all -failIfUnchanged [puddle, default_sub_properties, default_or_disjoint, OperationResult.isRefinedBy,
    Veir.CTree.interpretOp', Llvm.interpretOpCTree, Llvm.interpretOp', CTree.CanInterpretTo,
    RuntimeValue.isRefinedBy, integerConstant, constantBits, integerValue, bitwidth_of_integer,
    Attribute.of_def, IsAttr.inject, -Attribute.integerType_eq_of, normalize_integer_constant_bits]
  subst_vars
  simp_all -failIfUnchanged [puddle, RuntimeValue.isRefinedBy, Attribute.of_def, IsAttr.inject, -Attribute.integerType_eq_of]
  veir_bv_normalize))

private theorem sle_intMin_iff_eq (x : BitVec w) :
    x.sle (BitVec.intMin w) = true ↔ x = BitVec.intMin w := by
  constructor
  · intro h
    apply BitVec.eq_of_toInt_eq
    have hb := BitVec.toInt_intMin_le x
    simp only [BitVec.sle, decide_eq_true_eq] at h
    omega
  · intro h; subst x; simp [BitVec.sle]

private theorem intMax_sle_iff_eq (x : BitVec w) :
    (BitVec.intMax w).sle x = true ↔ x = BitVec.intMax w := by
  constructor
  · intro h
    apply BitVec.eq_of_toInt_eq
    have hb := BitVec.toInt_le (x := x)
    simp only [BitVec.sle, decide_eq_true_eq, BitVec.toInt_intMax] at h ⊢
    omega
  · intro h; subst x; simp [BitVec.sle]

private theorem sle_intMax (x : BitVec w) : x.sle (BitVec.intMax w) = true := by
  simp only [BitVec.sle, decide_eq_true_eq, BitVec.toInt_intMax]
  exact BitVec.toInt_le

end Veir.InstructionSimplify.CTreeProofs
