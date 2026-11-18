module

public import Veir.Data.LLVM.Int.Basic
public import Veir.Data.Casting
public import Veir.Dialects.GMIR.Semantics
public import Veir.Dialects.GMIR_RISCV.Semantics
meta import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide.Reflect
meta import Veir.Meta.Tactic.PBVDecide
public meta import Veir.PatternRewriter.Puddle.CTreeProofs
import Veir.ForLean
import all Veir.Data.LLVM.Int.Basic
import all Veir.Dialects.GMIR.Semantics
import all Veir.Dialects.GMIR.OpInfo
import all Veir.Dialects.GMIR_RISCV.Semantics
public import Veir.IR.Simp
public import Veir.IR.Attribute
import all Veir.PatternRewriter.Puddle.CTreeProofs
import all Veir.Passes.Legalization.LegalizerHelper
import all Veir.Passes.Legalization.LegalizationArtifactCombiner
import all Veir.Passes.Legalization.RISCV64LegalizerInfo
import all Veir.Passes.GMIRCombines.Combine
import all Veir.Dialects.GMIR.Interpreter
import all Veir.Dialects.GMIR_RISCV.OpInfo
import all Veir.GlobalOpInfo
import all Veir.Interpreter.Basic
import all Veir.Interpreter.CTreeInterpreter
import all Veir.IR.Attribute
import Veir.PatternRewriter.Puddle.Definitions
import Veir.PatternRewriter.Puddle.Validity
import Veir.PatternRewriter.Puddle.CTreeValidityTactics
import all Veir.Data.LLVM.Int.Bitblast
import all Init.Data.Array.Basic
import Veir.Meta.Tactic.BVDecide
meta import Veir.Meta.Tactic.BVDecide
meta import Veir.Meta.ProofKind
import all Veir.Dialects.GMIR.Properties
import all Init.Data.Nat.Power2.Basic
import all Veir.Passes.Legalization.Validity.Common
import all Veir.Passes.Legalization.Validity.PBVNormalize
import Veir.Passes.GMIRCombines.Simp
import Veir.Passes.Legalization.Proofs

/-!
# Correctness of the gMIR combines

The `Pattern.Valid` and `Status` theorems of the combines of `RISCV64PostLegalizerCombiner` and
`RISCV64PreLegalizerCombiner`, as for the RISC-V combines (`Veir.Passes.RISCVCombines.Proofs`): the
pattern unfolds by `simp only [gmir_pattern]`, `simpPuddleValid` discharges the structural
obligations, and `simp [puddle, gmir_combine]` unfolds the operation semantics, which are then
normalized at symbolic widths (`openCombineValid`). Most combines are then decided by
`pbv_decide` (`proveCombineValid`). The others are closed by a correctness lemma stated directly
above their validity theorem (`proveCombineValid using`), or by hand (`proveCombineValid with`).
-/

public section

namespace Veir.Data.LLVM

/-! ## gMIR combines

Definitions and tactics for the correctness lemmas of the gMIR combines, which are stated next to
the validity theorems at the end of this file. `combine_tac` unfolds the operations, splits their
poison checks, and closes the remaining bit-vector identity with `simp`, `omega` or `grind`'s ring
solver. The interpreters are written in the `Id` monad, so their poison checks are equations at
`Id (LLVM.Int w)`, which the `_id` lemmas below rewrite. -/

section Combines

/- Each case split of `combine_tac` uses part of its simp set. -/
set_option linter.unusedSimpArgs false

theorem ite_poison_eq_val_id {w : Nat} {c : Prop} [inst : Decidable c] {e : Id (LLVM.Int w)}
    {v : BitVec w} :
    @Eq (Id (LLVM.Int w)) (@ite (Id (LLVM.Int w)) c inst (@LLVM.Int.poison w) e)
      (@LLVM.Int.val w v) ↔ ¬c ∧ @Eq (Id (LLVM.Int w)) e (@LLVM.Int.val w v) := by
  split <;> simp_all

theorem val_eq_val_id {w : Nat} {a b : BitVec w} :
    @Eq (Id (LLVM.Int w)) (@LLVM.Int.val w a) (@LLVM.Int.val w b) ↔ a = b := by
  simp [Id]

theorem poison_eq_val_id {w : Nat} {b : BitVec w} :
    @Eq (Id (LLVM.Int w)) (@LLVM.Int.poison w) (@LLVM.Int.val w b) ↔ False := by
  simp [Id]

open Lean Meta in
/-- Split, recursively, each local conjunction, e.g. the poison checks an operation passed. -/
private meta partial def casesAnd (goal : MVarId) : MetaM (List MVarId) :=
  goal.withContext do
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      unless (← instantiateMVars decl.type).isAppOfArity ``And 2 do continue
      let subgoals ← goal.cases decl.fvarId
      return (← subgoals.toList.mapM fun subgoal => casesAnd subgoal.mvarId).flatten
    return [goal]

open Lean Elab Tactic in
elab "casesAnd" : tactic => do
  let goals ← getGoals
  setGoals (← goals.flatMapM fun goal => casesAnd goal)

macro "llvm_refines" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  (repeat' split) <;>
    try simp_all [Data.LLVM.Int.poison_isRefinedBy, Data.LLVM.Int.isRefinedBy_refl, Data.LLVM.Int.isRefinedBy_eq, ite_poison_eq_val_id, val_eq_val_id,
      poison_eq_val_id, $ls,*]
  all_goals casesAnd
  all_goals (try subst_vars)
  all_goals try simp_all [Data.LLVM.Int.poison_isRefinedBy, Data.LLVM.Int.isRefinedBy_refl, Data.LLVM.Int.isRefinedBy_eq, ite_poison_eq_val_id, val_eq_val_id,
      poison_eq_val_id, $ls,*]
  all_goals try (simp only [BitVec.le_def, BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_two_pow_self,
    BitVec.natCast_eq_ofNat, ge_iff_le] at *; omega)
  all_goals grind))

macro "combine_tac" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp only [Int.add, Int.sub, Int.and, Int.or, Int.xor, Int.shl, Int.lshr, Int.ashr, Int.icmp, Int.zext,
    Int.sext, Int.trunc, Int.bitreverse, Int.smin, Int.smax, Int.umin, Int.umax, GMIR.selectNonzero,
    Id.run, pure]
  llvm_refines [$ls,*]))

variable {w : Nat}

/-- The `i1` negation that `createNot` builds. -/
@[expose] def notI1 (c : LLVM.Int 1) : LLVM.Int 1 := LLVM.Int.xor c (LLVM.Int.constant 1 (-1))

/-- The predicate of the negated comparison, as `not_cmp_fold_pattern` pairs them. -/
@[expose] def IntPred.inverse : IntPred → IntPred
  | .eq => .ne | .ne => .eq | .ugt => .ule | .uge => .ult | .ult => .uge | .ule => .ugt
  | .sgt => .sle | .sge => .slt | .slt => .sge | .sle => .sgt

theorem IntPred.eval_inverse {v : Nat} (p : IntPred) (a b : BitVec v) :
    p.inverse.eval a b = !p.eval a b := by
  cases p <;> simp [IntPred.inverse, IntPred.eval, BitVec.ult, BitVec.ule, BitVec.slt, BitVec.sle,
    BitVec.lt_def, BitVec.le_def]
  all_goals first
    | rfl
    | simp [bne]
    | (rw [Bool.eq_iff_iff]; simp only [Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]; omega)

end Combines

end Veir.Data.LLVM

end

namespace Veir.GMIRCombines.CTreeProofs

open Puddle
open Puddle.CTree
open _root_.CTree
open Veir.Legalization.CTreeProofs

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

attribute [local puddle]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  GMIR.interpretOp' GMIR.interpretOpCTree GMIR_RISCV.interpretOp' GMIR_RISCV.base

/- The builders of `Veir.Passes.Legalization.LegalizerHelper` that the combines use. -/
attribute [local gmir_pattern]
  matchLegalInt createConstantWith createConstant widthConstant createSextInReg

attribute [local gmir_combine]
  Attribute.of _root_.CTree.CTree.bind_tau Sim.tau_l Sim.bind_monadLift_right_iff

attribute [local implicit_reducible] TypeAttr

/-! ## Tactics

An operation that a combine creates has the default properties of its opcode: no `nsw`, `nuw`,
`exact`, `disjoint` or `nneg` flag. -/

@[gmir_combine]
theorem default_g_add :
    (default : propertiesOf (OpCode.gmir .g_add)) = ({ nsw := false, nuw := false } : NswNuwProperties) :=
  rfl

@[gmir_combine]
theorem default_g_sub :
    (default : propertiesOf (OpCode.gmir .g_sub)) = ({ nsw := false, nuw := false } : NswNuwProperties) :=
  rfl

@[gmir_combine]
theorem default_g_mul :
    (default : propertiesOf (OpCode.gmir .g_mul)) = ({ nsw := false, nuw := false } : NswNuwProperties) :=
  rfl

@[gmir_combine]
theorem default_g_shl :
    (default : propertiesOf (OpCode.gmir .g_shl)) = ({ nsw := false, nuw := false } : NswNuwProperties) :=
  rfl

@[gmir_combine]
theorem default_g_trunc :
    (default : propertiesOf (OpCode.gmir .g_trunc)) = ({ nsw := false, nuw := false } : NswNuwProperties) :=
  rfl

@[gmir_combine]
theorem default_g_sdiv :
    (default : propertiesOf (OpCode.gmir .g_sdiv)) = ({ exact := false } : ExactProperties) := rfl

@[gmir_combine]
theorem default_g_udiv :
    (default : propertiesOf (OpCode.gmir .g_udiv)) = ({ exact := false } : ExactProperties) := rfl

@[gmir_combine]
theorem default_g_lshr :
    (default : propertiesOf (OpCode.gmir .g_lshr)) = ({ exact := false } : ExactProperties) := rfl

@[gmir_combine]
theorem default_g_ashr :
    (default : propertiesOf (OpCode.gmir .g_ashr)) = ({ exact := false } : ExactProperties) := rfl

@[gmir_combine]
theorem default_g_or :
    (default : propertiesOf (OpCode.gmir .g_or)) = ({ disjoint := false } : DisjointProperties) := rfl

@[gmir_combine]
theorem default_g_zext :
    (default : propertiesOf (OpCode.gmir .g_zext)) = ({ nneg := false } : NnegProperties) := rfl

/-- The predicates the combines test on a matched constant, read at the width of its result. -/
macro "simpConstantPreds" : tactic => `(tactic|
  simp only [GMIRConstantProperties.bits, GMIRConstantProperties.isZero, GMIRConstantProperties.isOne,
    GMIRConstantProperties.isAllOnes, GMIRConstantProperties.isMinSigned, GMIRConstantProperties.neg,
    GMIRConstantProperties.isOffsetOf, GMIRConstantProperties.log2?, GMIRConstantProperties.ulog2?,
    GMIRConstantProperties.slog2?, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq, Bool.or_eq_true] at *)

/-- Normalize the goals of a combine that matches constants: split each constant's properties and
substitute its type, which `matchConstant` equates to the result type, so that each constant is
`BitVec.ofInt w v` at its result width `w`. -/
macro "normalizeConstants" : tactic => `(tactic| (
  all_goals intros
  all_goals (casesLocalsOf GMIRConstantProperties IntegerAttr)
  all_goals casesIntegerTypes
  all_goals (try simp only [IntegerType.mk.injEq] at *)
  all_goals (try casesExistsAnd)
  all_goals (try subst_vars)
  all_goals (try simpConstantPreds)))

open Veir.Data Veir.Data.LLVM in
/--
A widened `g_icmp` result is poison, zero or one: apply this to `LLVM.Int.icmp x y pred`.
These are the nonconstant arms matched by `matchBoolArm`; the constant arms are zero or one
directly.
-/
private theorem zext_i1_eq_poison_or_zero_or_one {w : Nat} (h : 1 < w) (c : LLVM.Int 1) :
    LLVM.Int.zext c w false h = .poison ∨
    LLVM.Int.zext c w false h = .val 0#w ∨
    LLVM.Int.zext c w false h = .val 1#w := by
  cases c with
  | poison => simp [LLVM.Int.zext, Id.run]
  | val c =>
    rcases BitVec.eq_zero_or_eq_one c with rfl | rfl <;>
      simp [LLVM.Int.zext, Id.run,
        BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt (by decide : 0 < 1)]

open Veir.Data Veir.Data.LLVM in
/-- An `i1` comparison arm of `redundant_and_select_pattern` is poison, zero or one. -/
private theorem icmp_eq_poison_or_zero_or_one {v : Nat} (x y : LLVM.Int v) (p : IntPred) :
    x.icmp y p = .poison ∨ x.icmp y p = .val 0#1 ∨ x.icmp y p = .val 1#1 := by
  cases x <;> cases y <;> simp [LLVM.Int.icmp, Id.run]
  rename_i a b
  cases p.eval a b <;> simp

open Veir.Data Veir.Data.LLVM in
/-- A constant arm of `redundant_and_select_pattern` is zero or one. -/
private theorem boolArm_of_constant {w : Nat} (c : BitVec w) (h : c = 0 ∨ c = 1) :
    LLVM.Int.val c = .poison ∨ LLVM.Int.val c = .val 0#w ∨ LLVM.Int.val c = .val 1#w := by
  rcases h with rfl | rfl <;> simp

/-- Closes a hypothesis of a local correctness lemma: a predicate of the matcher, or a
comparison or constant arm that is zero or one. -/
macro "closeConstSide" : tactic => `(tactic| first
  | assumption
  | exact zext_i1_eq_poison_or_zero_or_one ‹_› _
  | exact icmp_eq_poison_or_zero_or_one _ _ _
  | exact boolArm_of_constant _ ‹_›
  | simp_all
  | omega)

/-- Closes a value goal with the first of the lemmas that applies. -/
syntax "closeConstWith" term,+ : tactic
macro_rules
  | `(tactic| closeConstWith $l) => `(tactic| (apply $l <;> closeConstSide))
  | `(tactic| closeConstWith $l, $ls,*) =>
    `(tactic| first | (apply $l <;> closeConstSide) | closeConstWith $ls,*)

/-- Unfold the pattern of a gMIR combine, discharge the structural obligations, and unfold the
semantics of its operations. -/
macro "simpCombineSemantics" : tactic => `(tactic| (
  /- Also resolve the choices that a pattern makes on its `Bool` arguments. -/
  simp only [gmir_pattern, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false, Bool.bne_true,
    Bool.bne_false, Bool.not_false, Bool.not_true]
  simpPuddleValid
  simp [puddle, gmir_combine, -Attribute.integerType_eq_of]))

/-- Open the validity goal of a gMIR combine: `simpCombineSemantics`, then normalize the semantics
down to the values of the matched operations at symbolic widths, and split the properties of each
matched constant, so that it reads `BitVec.ofInt w v` at its result width `w`, with the matcher's
predicate as a hypothesis on it. -/
macro "openCombineValid" : tactic => `(tactic| (
  simpCombineSemantics
  normalizeLegalValid
  normalizeConstants
  /- Strip the truncations of extended values that a narrow operation reads back, and the
  zero extensions of `g_icmp` results to their result type, on both sides or in a condition. -/
  all_goals (try simp only [Data.LLVM.trunc_ext, Data.LLVM.trunc_sext,
    Data.LLVM.zext_isRefinedBy_zext, Data.LLVM.selectNonzero_zext, Data.LLVM.Int.isRefinedBy_refl])))

/-- Prove the validity of a gMIR combine by `pbv_decide`, bit-blasting at width 64 when it does not
decide the goal at symbolic widths. -/
macro "proveCombineValid" : tactic => `(tactic| (
  openCombineValid
  all_goals first
    | (veir_pbv_decide 64 (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))
    | (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false)
       all_goals bv_decide (config := { timeout := 300 }))))

/-- Prove the validity of a gMIR combine, closing each value goal with the first of the local
correctness lemmas `ls` that applies. -/
macro "proveCombineValid" "using" ls:term,+ : tactic => `(tactic| (
  openCombineValid
  all_goals closeConstWith $ls,*))

/-- Prove the validity of a gMIR combine, closing the value goals with the tactics `closer`. -/
macro "proveCombineValid" "with" closer:tacticSeq : tactic => `(tactic| (
  openCombineValid
  all_goals ($closer)))

/-! ## Combines

The combines whose values are not constants, and that `pbv_decide` does not decide alone. -/

/-- `canonicalize_icmp_pattern`: swapping the operands of a comparison swaps its predicate. -/
@[combine_valid, proof_pbv]
theorem combine_canonicalize_icmp_valid : Puddle.CTree.Pattern.Valid canonicalize_icmp_pattern := by
  proveCombineValid with
    (casesLocalsOf Data.LLVM.IntPred)
    all_goals (try simp only [swapIntPred, Data.LLVM.IntPred.inverse] at *)
    all_goals (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

/-- The low bit of an odd constant is set. -/
private theorem one_and_ofInt_of_odd {W : Nat} (hW : 0 < W) (v : _root_.Int) (hv : v % 2 = 1) :
    1#W &&& BitVec.ofInt W v = 1#W := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_and, BitVec.getElem_one]
  by_cases h : i = 0
  · subst h
    simp only [decide_true, Bool.true_and, BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofInt,
      Nat.testBit_zero, decide_eq_true_eq]
    have hd : (2 : _root_.Int) ∣ ((2 ^ W : Nat) : _root_.Int) := by
      refine ⟨((2 ^ (W - 1) : Nat) : _root_.Int), ?_⟩
      rw [show W = (W - 1) + 1 by omega, Nat.pow_succ]
      push_cast
      rw [_root_.Int.mul_comm]
    have h1 : (v % ((2 ^ W : Nat) : _root_.Int)) % 2 = 1 := by
      rw [_root_.Int.emod_emod_of_dvd _ hd]; exact hv
    have h0 : 0 ≤ v % ((2 ^ W : Nat) : _root_.Int) :=
      _root_.Int.emod_nonneg _ (by have := Nat.two_pow_pos W; omega)
    omega
  · simp [h]

/-- `redundant_and_pattern`, for an `i1` result: masking a comparison with an odd constant keeps it. -/
private theorem and_icmp_odd {v : Nat} (x y : Data.LLVM.Int v) (p : Data.LLVM.IntPred) (c : _root_.Int)
    (hc : c % 2 = 1) : (x.icmp y p).and (.val (BitVec.ofInt 1 c)) ⊒ x.icmp y p := by
  have := one_and_ofInt_of_odd (W := 1) (by decide) c hc
  cases x <;> cases y <;> simp only [Data.LLVM.Int.icmp, Data.LLVM.Int.and, Id.run, Data.LLVM.Int.isRefinedBy_eq, pure]
  rename_i a b
  cases Data.LLVM.IntPred.eval p a b <;> simp_all

/-- `redundant_and_pattern`, for a wider result: the comparison is zero-extended to `0` or `1`. -/
private theorem and_zext_icmp_odd {v W : Nat} (x y : Data.LLVM.Int v) (p : Data.LLVM.IntPred) (c : _root_.Int)
    (hc : c % 2 = 1) (hW : 1 < W) :
    ((x.icmp y p).zext W false hW).and (.val (BitVec.ofInt W c)) ⊒ (x.icmp y p).zext W false hW := by
  have := one_and_ofInt_of_odd (W := W) (by omega) c hc
  cases x <;> cases y <;>
    simp only [Data.LLVM.Int.icmp, Data.LLVM.Int.and, Data.LLVM.Int.zext, Id.run, Data.LLVM.Int.isRefinedBy_eq, pure]
  rename_i a b
  have h1 : BitVec.setWidth W 1#1 = 1#W := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth, Nat.one_mod_two_pow (by omega : 0 < W)]
  cases Data.LLVM.IntPred.eval p a b <;> simp_all [BitVec.setWidth_eq]

/-- `redundant_and_select_pattern .icmp .icmp`, for an `i1` result: both arms are comparisons. -/
private theorem and_select_icmp_odd {wc v₁ v₂ : Nat} (c : Data.LLVM.Int wc) (x y : Data.LLVM.Int v₁)
    (x' y' : Data.LLVM.Int v₂) (p q : Data.LLVM.IntPred) (k : _root_.Int) (hk : k % 2 = 1) :
    (GMIR.selectNonzero c (x.icmp y p) (x'.icmp y' q)).and (.val (BitVec.ofInt 1 k)) ⊒
      GMIR.selectNonzero c (x.icmp y p) (x'.icmp y' q) := by
  cases c with
  | poison => simp [GMIR.selectNonzero, Data.LLVM.Int.and, Id.run, Data.LLVM.Int.poison_isRefinedBy]
  | val c =>
    by_cases h : c = 0#wc <;> simp only [GMIR.selectNonzero, Id.run, h, bne_self_eq_false, ite_false,
      ite_true, bne_iff_ne, ne_eq, not_false_eq_true, Bool.false_eq_true]
    · exact and_icmp_odd x' y' q k hk
    · exact and_icmp_odd x y p k hk

/-- `redundant_and_select_pattern .icmp .icmp`, for a wider result. -/
private theorem and_select_zext_icmp_odd {wc v₁ v₂ W : Nat} (c : Data.LLVM.Int wc) (x y : Data.LLVM.Int v₁)
    (x' y' : Data.LLVM.Int v₂) (p q : Data.LLVM.IntPred) (k : _root_.Int) (hk : k % 2 = 1) (hW : 1 < W) :
    (GMIR.selectNonzero c ((x.icmp y p).zext W false hW) ((x'.icmp y' q).zext W false hW)).and
        (.val (BitVec.ofInt W k)) ⊒
      GMIR.selectNonzero c ((x.icmp y p).zext W false hW) ((x'.icmp y' q).zext W false hW) := by
  cases c with
  | poison => simp [GMIR.selectNonzero, Data.LLVM.Int.and, Id.run, Data.LLVM.Int.poison_isRefinedBy]
  | val c =>
    by_cases h : c = 0#wc <;> simp only [GMIR.selectNonzero, Id.run, h, bne_self_eq_false, ite_false,
      ite_true, bne_iff_ne, ne_eq, not_false_eq_true, Bool.false_eq_true]
    · exact and_zext_icmp_odd x' y' q k hk hW
    · exact and_zext_icmp_odd x y p k hk hW

set_option maxHeartbeats 8000000 in
/-- The two comparisons and the constant make this the slowest combine to normalize. -/
@[combine_valid, proof_manual]
theorem combine_redundant_and_select_icmp_icmp_valid :
    Puddle.CTree.Pattern.Valid (redundant_and_select_pattern .icmp .icmp) := by
  proveCombineValid with first
    | (apply and_select_zext_icmp_odd <;> assumption)
    | (apply and_select_icmp_odd <;> assumption)

@[combine_valid, proof_manual]
theorem combine_redundant_and_valid : Puddle.CTree.Pattern.Valid redundant_and_pattern := by
  proveCombineValid with first
    | (apply and_zext_icmp_odd <;> assumption)
    | (apply and_icmp_odd <;> assumption)

/-! ### Funnel shifts or-ed with the shift they subsume

`(fshl x z y) | (x << y) → fshl x z y` and `(z >> y) | (fshr x z y) → fshr x z y`, in both orders:
the plain shift's bits are among the funnel shift's when the amount is in range, and it is poison
otherwise. -/

/-- The bits of `x << s` are among those of `fshl x z s`, for `s < w`. -/
private theorem fshl_or_shl_bits {w : Nat} (x z : BitVec w) (s : Nat) :
    ((x ++ z) <<< s).extractLsb' w w ||| x <<< s = ((x ++ z) <<< s).extractLsb' w w := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_or, BitVec.getElem_extractLsb', BitVec.getElem_shiftLeft,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append]
  by_cases h : i < s
  · simp [h]
  · have : ¬ w + i < s := by omega
    simp only [h, this, decide_false, Bool.not_false, Bool.true_and, show w + i < w + w by omega,
      decide_true, show ¬ (w + i - s < w) by omega, ite_false, BitVec.getLsbD_eq_getElem (by omega : i - s < w),
      show w + i - s - w = i - s by omega]
    simp

private theorem fshl_or_shl {w v : Nat} (x z : Data.LLVM.Int w) (y : Data.LLVM.Int v) (n u d : Bool) :
    (x.fshl z (GMIR.funnelShiftAmount w y)).or (x.shl (shiftAmount w y) n u) d ⊒
      x.fshl z (GMIR.funnelShiftAmount w y) := by
  cases x <;> cases z <;> cases y <;>
    simp [GMIR.funnelShiftAmount, shiftAmount, Data.LLVM.Int.fshl, Data.LLVM.Int.shl, Data.LLVM.Int.or,
      Id.run, Data.LLVM.Int.poison_isRefinedBy, pure]
  rename_i x z y
  by_cases h : y.toNat < w
  · have hw : w < 2 ^ w := Nat.lt_two_pow_self
    have hsw : (BitVec.setWidth w y).toNat = y.toNat := by
      simp only [BitVec.toNat_setWidth]
      exact Nat.mod_eq_of_lt (by omega)
    have hm : y.toNat % w % 2 ^ w % w = y.toNat := by
      rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (show y.toNat < 2 ^ w by omega), Nat.mod_eq_of_lt h]
    have hlt : ¬ BitVec.ofNat w w ≤ BitVec.setWidth w y := by
      simp only [BitVec.le_def, hsw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]
      omega
    simp only [h, ite_true, hlt, ite_false, hsw, hm]
    split
    · rename_i y' heq
      simp only [Data.LLVM.ite_poison_eq_val_id, Data.LLVM.val_eq_val_id] at heq
      obtain ⟨-, -, rfl⟩ := heq
      split <;> simp [Data.LLVM.Int.poison_isRefinedBy, Data.LLVM.Int.isRefinedBy_eq, fshl_or_shl_bits]
    · simp [Data.LLVM.Int.poison_isRefinedBy]
  · have hge : BitVec.ofNat w w ≤ BitVec.allOnes w := by
      have := Nat.lt_two_pow_self (n := w)
      simp [BitVec.le_def, BitVec.toNat_allOnes, Nat.mod_eq_of_lt this]
      omega
    simp [h, hge, Data.LLVM.Int.poison_isRefinedBy]

/-- `g_or` is commutative, including its `disjoint` check. -/
private theorem or_comm' {w : Nat} (a b : Data.LLVM.Int w) (d : Bool) : a.or b d = b.or a d := by
  cases a <;> cases b <;> simp [Data.LLVM.Int.or, Id.run, BitVec.or_comm, BitVec.and_comm]

private theorem shl_or_fshl {w v : Nat} (x z : Data.LLVM.Int w) (y : Data.LLVM.Int v) (n u d : Bool) :
    (x.shl (shiftAmount w y) n u).or (x.fshl z (GMIR.funnelShiftAmount w y)) d ⊒
      x.fshl z (GMIR.funnelShiftAmount w y) := by
  rw [or_comm']
  exact fshl_or_shl x z y n u d

@[combine_valid, proof_manual]
theorem combine_funnel_shift_fshl_or_shl_valid :
    Puddle.CTree.Pattern.Valid (funnel_shift_or_shift_pattern .g_fshl .g_shl true true) := by
  proveCombineValid using fshl_or_shl

@[combine_valid, proof_manual]
theorem combine_funnel_shift_shl_or_fshl_valid :
    Puddle.CTree.Pattern.Valid (funnel_shift_or_shift_pattern .g_fshl .g_shl true false) := by
  proveCombineValid using shl_or_fshl

/-! ## Status of every combine -/

@[legalization_status]
theorem combine_funnel_shift_fshl_or_shl_status :
    Status Unproven (funnel_shift_or_shift_pattern .g_fshl .g_shl true true) :=
  .proven combine_funnel_shift_fshl_or_shl_valid

@[legalization_status]
theorem combine_funnel_shift_shl_or_fshl_status :
    Status Unproven (funnel_shift_or_shift_pattern .g_fshl .g_shl true false) :=
  .proven combine_funnel_shift_shl_or_fshl_valid

@[legalization_status]
theorem combine_canonicalize_icmp_status :
    Status Unproven canonicalize_icmp_pattern :=
  .proven (combine_canonicalize_icmp_valid )

@[legalization_status]
theorem combine_redundant_and_status : Status Unproven redundant_and_pattern :=
  .proven combine_redundant_and_valid

@[legalization_status]
theorem combine_redundant_and_select_icmp_icmp_status :
    Status Unproven (redundant_and_select_pattern .icmp .icmp) :=
  .proven combine_redundant_and_select_icmp_icmp_valid

/-! ## Combines that match constants

The combines that test or compute the value of a matched `g_constant`.

`matchConstant` requires the constant's attribute to have the type of its result, as the verifier
does, so the combines read the constant at the width it has: `normalizeConstants` splits its
properties and substitutes that type, which leaves each constant as `BitVec.ofInt w v` with the
matcher's predicate as a hypothesis on it. Each goal is then closed by a lemma stated for an
arbitrary constant `c`, directly above the validity theorem that uses it.

Two matchers also needed a typing condition: `select_into_binop_pattern` skips `i0`, where the
shift by the created `0` is out of range, and `matchFunnelShiftConstAmt` matches the result at the
type of the shifted value, since `funnel_shift_overshift_pattern` reduces the amount modulo the
result width while the funnel shift takes it modulo the width of its operands. -/

/-! ### Multiplications and subtractions by a matched constant -/

open Veir.Data Veir.Data.LLVM in
private theorem right_identity_one_mul {w : Nat} (x : LLVM.Int w) (c : BitVec w) (hc : c.toNat = 1) (n u : Bool) :
    x.mul (.val c) n u ⊒ x := by
  have : c = 1#w := by
    apply BitVec.eq_of_toNat_eq; rw [hc]
    have : 1 < 2 ^ w := by
      rcases Nat.lt_or_ge 1 (2 ^ w) with h | h
      · exact h
      · have := c.isLt; omega
    simp [Nat.mod_eq_of_lt this]
  subst this
  cases x <;> simp only [LLVM.Int.mul, Id.run, pure] <;>
    llvm_refines [BitVec.mul_zero, BitVec.zero_mul, BitVec.mul_one]

@[combine_valid, proof_manual]
theorem combine_right_identity_one_int_valid :
    Puddle.CTree.Pattern.Valid (right_identity_one_int_pattern) := by
  proveCombineValid using right_identity_one_mul

open Veir.Data Veir.Data.LLVM in
private theorem sub_one_from_sub {w : Nat} (x y : LLVM.Int w) (c : BitVec w) (hc : c.toInt = 1) (n₁ u₁ n₂ u₂ : Bool) :
    (x.sub y n₁ u₁).sub (.val c) n₂ u₂ ⊒ (y.xor (.val (BitVec.ofInt w (-1)))).add x := by
  have : c = 1#w := by
    rw [← BitVec.ofInt_toInt (x := c), hc]; simp
  subst this
  have hsub (a b : BitVec w) : a - b - 1#w = ~~~b + a := by
    rw [BitVec.not_eq_neg_add]; simp only [BitVec.sub_eq_add_neg]; ac_rfl
  rw [ofInt_neg_one]
  cases x <;> cases y <;> combine_tac [BitVec.xor_allOnes, hsub]

@[combine_valid, proof_manual]
theorem combine_sub_one_from_sub_valid :
    Puddle.CTree.Pattern.Valid (sub_one_from_sub_pattern) := by
  proveCombineValid using sub_one_from_sub

open Veir.Data Veir.Data.LLVM in
private theorem ofInt_neg_toInt {w : Nat} (x : BitVec w) : BitVec.ofInt w (-x.toInt) = -x := by
  apply BitVec.eq_of_toInt_eq; simp [BitVec.toInt_ofInt, BitVec.toInt_neg]

open Veir.Data Veir.Data.LLVM in
private theorem sub_of_mul_const {w : Nat} (a x : LLVM.Int w) (c : BitVec w) (n₁ u₁ n₂ u₂ : Bool) :
    a.sub (x.mul (.val c) n₁ u₁) n₂ u₂ ⊒ a.add (x.mul (.val (BitVec.ofInt w (-c.toInt)))) := by
  rw [ofInt_neg_toInt]
  cases a <;> cases x <;> simp only [LLVM.Int.mul, Id.run, pure] <;>
    combine_tac [BitVec.mul_neg, BitVec.sub_eq_add_neg]

@[combine_valid, proof_manual]
theorem combine_sub_of_mul_const_valid :
    Puddle.CTree.Pattern.Valid (sub_of_mul_const_pattern) := by
  proveCombineValid using sub_of_mul_const

open Veir.Data Veir.Data.LLVM in
private theorem mul_by_neg_one {w : Nat} (x : LLVM.Int w) (c : BitVec w) (hc : c = -1) (n u : Bool) :
    x.mul (.val c) n u ⊒ (LLVM.Int.val 0#w).sub x n := by
  subst hc
  cases x with
  | poison => simp [LLVM.Int.mul, Id.run, Data.LLVM.Int.poison_isRefinedBy]
  | val x =>
    have hov : BitVec.smulOverflow x (-1#w) = BitVec.ssubOverflow 0#w x := by
      rcases Nat.eq_zero_or_pos w with rfl | hw
      · simp [BitVec.smulOverflow, BitVec.ssubOverflow, BitVec.toInt_of_zero_length]
      have hm : (-1#w).toInt = -1 := by
        rw [BitVec.neg_one_eq_allOnes, BitVec.toInt_allOnes]; simp [hw]
      simp only [BitVec.smulOverflow, BitVec.ssubOverflow, hm, BitVec.toInt_zero]
      congr 1 <;> simp <;> omega
    simp only [LLVM.Int.mul, LLVM.Int.sub, Id.run, pure, hov]
    llvm_refines [BitVec.mul_neg, BitVec.mul_one, BitVec.zero_sub]

@[combine_valid, proof_manual]
theorem combine_mul_by_neg_one_valid :
    Puddle.CTree.Pattern.Valid (mul_by_neg_one_pattern) := by
  proveCombineValid using mul_by_neg_one

open Veir.Data Veir.Data.LLVM in
private theorem mulo_by_2 {w : Nat} (x : LLVM.Int w) (c : BitVec w) (hc : c.toInt = 2) (n u : Bool) :
    x.mul (.val c) n u ⊒ x.add x n u := by
  have hn : c.toNat = 2 := by
    have := BitVec.toInt_eq_toNat_of_msb (x := c); grind [BitVec.toInt_eq_toNat_cond]
  cases x with
  | poison => simp [LLVM.Int.mul, Id.run, Data.LLVM.Int.poison_isRefinedBy]
  | val x =>
    have hs : BitVec.smulOverflow x c = BitVec.saddOverflow x x := by
      simp only [BitVec.smulOverflow, BitVec.saddOverflow, hc]; congr 1 <;> simp <;> omega
    have hu : BitVec.umulOverflow x c = BitVec.uaddOverflow x x := by
      simp only [BitVec.umulOverflow, BitVec.uaddOverflow, hn]; congr 1; simp; omega
    have hv : x * c = x + x := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_mul, BitVec.toNat_add, hn, Nat.mul_two]
    simp only [LLVM.Int.mul, LLVM.Int.add, Id.run, hs, hu, hv]
    exact Data.LLVM.Int.isRefinedBy_refl _

@[combine_valid, proof_manual]
theorem combine_mulo_by_2_valid :
    Puddle.CTree.Pattern.Valid (mulo_by_2_pattern) := by
  proveCombineValid using mulo_by_2

/-! ### Negated comparisons -/

open Veir.Data Veir.Data.LLVM in
private theorem not_cmp_fold {v : Nat} (x y : LLVM.Int v) (p : IntPred) (c : BitVec 1) (hc : c.toNat = 1) :
    (x.icmp y p).xor (.val c) ⊒ x.icmp y p.inverse := by
  have : c = 1#1 := BitVec.eq_of_toNat_eq (by simp [hc])
  subst this
  cases x <;> cases y <;> simp [LLVM.Int.icmp, LLVM.Int.xor, Id.run, Data.LLVM.Int.poison_isRefinedBy,
    IntPred.eval_inverse]
  rename_i a b
  cases p.eval a b <;> exact Data.LLVM.Int.isRefinedBy_refl _

open Veir.Data Veir.Data.LLVM in
private theorem not_cmp_fold_zext {v W : Nat} (x y : LLVM.Int v) (p : IntPred) (h : 1 < W) (c : BitVec W)
    (hc : c.toNat = 1) :
    ((x.icmp y p).zext W false h).xor (.val c) ⊒ (x.icmp y p.inverse).zext W false h := by
  have : c = 1#W := BitVec.eq_of_toNat_eq (by
    simp [hc, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h (Nat.le_of_lt Nat.lt_two_pow_self))])
  subst this
  cases x <;> cases y <;> simp [LLVM.Int.icmp, LLVM.Int.xor, LLVM.Int.zext, Id.run,
    Data.LLVM.Int.poison_isRefinedBy, IntPred.eval_inverse]
  rename_i a b
  cases p.eval a b <;>
    simp [BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt (by decide : 0 < 1), Data.LLVM.Int.isRefinedBy_refl]

@[combine_valid, proof_manual]
theorem combine_not_cmp_fold_eq_valid :
    Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .eq .ne) := by
  proveCombineValid using not_cmp_fold_zext, not_cmp_fold

@[combine_valid, proof_manual]
theorem combine_not_cmp_fold_ne_valid :
    Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .ne .eq) := by
  proveCombineValid using not_cmp_fold_zext, not_cmp_fold

@[combine_valid, proof_manual]
theorem combine_not_cmp_fold_ugt_valid :
    Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .ugt .ule) := by
  proveCombineValid using not_cmp_fold_zext, not_cmp_fold

@[combine_valid, proof_manual]
theorem combine_not_cmp_fold_uge_valid :
    Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .uge .ult) := by
  proveCombineValid using not_cmp_fold_zext, not_cmp_fold

@[combine_valid, proof_manual]
theorem combine_not_cmp_fold_ult_valid :
    Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .ult .uge) := by
  proveCombineValid using not_cmp_fold_zext, not_cmp_fold

@[combine_valid, proof_manual]
theorem combine_not_cmp_fold_ule_valid :
    Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .ule .ugt) := by
  proveCombineValid using not_cmp_fold_zext, not_cmp_fold

@[combine_valid, proof_manual]
theorem combine_not_cmp_fold_sgt_valid :
    Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .sgt .sle) := by
  proveCombineValid using not_cmp_fold_zext, not_cmp_fold

@[combine_valid, proof_manual]
theorem combine_not_cmp_fold_sge_valid :
    Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .sge .slt) := by
  proveCombineValid using not_cmp_fold_zext, not_cmp_fold

@[combine_valid, proof_manual]
theorem combine_not_cmp_fold_slt_valid :
    Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .slt .sge) := by
  proveCombineValid using not_cmp_fold_zext, not_cmp_fold

@[combine_valid, proof_manual]
theorem combine_not_cmp_fold_sle_valid :
    Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .sle .sgt) := by
  proveCombineValid using not_cmp_fold_zext, not_cmp_fold

/-! ### Powers of two

The matcher reads a power of two `±2^k` with `exactLog2?`, and the rewrite shifts by `k`.

The combines are proved for every width `w`. The divisor is the constant `±2^k`, and the created
shift amounts are the constants `k`, `w - 1` and `w - k`. -/

private theorem exactLog2?_eq_some {n k : Nat} (h : exactLog2? n = some k) : n = 2 ^ k := by
  unfold exactLog2? at h
  split at h
  · rename_i hn
    obtain ⟨j, rfl⟩ : ∃ j, n = 2 ^ j := Nat.ne_zero_and_sub_one_eq_zero_iff_isPowerOfTwo.mp hn
    simp only [Option.some.injEq, Nat.log2_two_pow] at h
    rw [h]
  · cases h

private theorem shiftAmount_ofNat {w k : Nat} (hk : k < w) :
    shiftAmount w (Data.LLVM.Int.val (BitVec.ofNat w k)) = Data.LLVM.Int.constant w k := by
  have : k < 2 ^ w := Nat.lt_trans hk Nat.lt_two_pow_self
  simp [shiftAmount, Data.LLVM.Int.constant, Nat.mod_eq_of_lt this, hk]

private theorem udiv_pow2 {w : Nat} (x : Data.LLVM.Int w) (c : BitVec w)
    (hc : (exactLog2? c.toNat).isSome = true) (e : Bool) :
    x.udiv (.val c) e ⊒
      x.lshr (shiftAmount w (.val (BitVec.ofNat w (exactLog2? c.toNat).get!))) := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hc
  have hc2 := exactLog2?_eq_some hk
  have hkw : k < w := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (hc2 ▸ c.isLt)
  have : c = BitVec.twoPow w k :=
    BitVec.eq_of_toNat_eq (by rw [hc2, BitVec.toNat_twoPow_of_lt hkw])
  rw [hk, Option.get!_some, shiftAmount_ofNat hkw, this]
  veir_bv_normalize
  grind [BitVec.lt_ofInt_natCast_ofNat_of_lt, BitVec.toNat_ofInt_natCast_of_lt,
    BitVec.udiv_twoPow_eq_of_lt]

@[combine_valid, proof_manual]
theorem combine_udiv_by_pow2_valid :
    Puddle.CTree.Pattern.Valid (udiv_by_pow2_pattern) := by
  proveCombineValid using udiv_pow2

private theorem two_pow_cast (k : Nat) : ((2 ^ k : Nat) : Int) = 2 ^ k := by push_cast; rfl

/-- A constant `2^k` that is positive as a signed integer. -/
private theorem eq_twoPow_of_toInt {w k : Nat} {c : BitVec w} (h : c.toInt = 2 ^ k) :
    k + 1 < w ∧ c = BitVec.twoPow w k := by
  have hc := BitVec.toInt_eq_toNat_cond c
  have hP := two_pow_cast k
  have hQ := two_pow_cast w
  have := c.isLt
  have := Nat.one_le_two_pow (n := k)
  have hn : c.toNat = 2 ^ k ∧ 2 * 2 ^ k < 2 ^ w := by
    split at hc <;> omega
  have hk : k + 1 < w := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (by rw [Nat.pow_succ]; omega)
  exact ⟨hk, BitVec.eq_of_toNat_eq (by rw [hn.1, BitVec.toNat_twoPow_of_lt (by omega)])⟩

/-- The signed power of two `±2^k` that `slog2?` reads. -/
private theorem slog2_some {w k : Nat} {c : BitVec w} (hk : exactLog2? c.toInt.natAbs = some k) :
    (c.toInt < 0 → c.toInt = -2 ^ k) ∧ (¬ c.toInt < 0 → c.toInt = 2 ^ k) := by
  have habs := exactLog2?_eq_some hk
  have hP := two_pow_cast k
  constructor <;> intro hneg <;> omega

private theorem sdiv_exact_pow2_pos {w : Nat} (x : Data.LLVM.Int w) (c : BitVec w)
    (h : Option.any (fun x => !x.snd)
      (Option.map (fun x => (x, decide (c.toInt < 0))) (exactLog2? c.toInt.natAbs)) = true) :
    x.sdiv (.val c) true ⊒
      x.ashr (shiftAmount w (.val (BitVec.ofNat w
        (Option.map (fun x => (x, decide (c.toInt < 0))) (exactLog2? c.toInt.natAbs)).get!.fst))) := by
  cases hk : exactLog2? c.toInt.natAbs with
  | none => simp [hk] at h
  | some k =>
    simp only [hk, Option.map_some, Option.any_some, Bool.not_eq_true', decide_eq_false_iff_not] at h
    simp only [Option.map_some, Option.get!_some]
    obtain ⟨hkw, rfl⟩ := eq_twoPow_of_toInt ((slog2_some hk).2 h)
    rw [shiftAmount_ofNat (by omega)]
    veir_bv_normalize
    grind [BitVec.twoPow_eq_shiftLeft_one_ofInt_natCast, BitVec.lt_ofInt_natCast_ofNat_of_lt,
      BitVec.toNat_ofInt_natCast_of_lt, BitVec.sdiv_one_shl_of_smod_eq_zero]

@[combine_valid, proof_manual]
theorem combine_sdiv_exact_by_pow2_pos_valid :
    Puddle.CTree.Pattern.Valid (sdiv_exact_by_pow2_pattern false) := by
  proveCombineValid using sdiv_exact_pow2_pos

/-- A constant `-2^k`, including the minimum signed value. -/
private theorem eq_neg_twoPow_of_toInt {w k : Nat} {c : BitVec w} (h : c.toInt = -2 ^ k) :
    k < w ∧ c = -BitVec.twoPow w k := by
  have hc := BitVec.toInt_eq_toNat_cond c
  have hP := two_pow_cast k
  have hQ := two_pow_cast w
  have := c.isLt
  have := Nat.one_le_two_pow (n := k)
  have hn : c.toNat = 2 ^ w - 2 ^ k ∧ 2 ^ k < 2 ^ w := by
    split at hc <;> omega
  have hk : k < w := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hn.2
  refine ⟨hk, BitVec.eq_of_toNat_eq ?_⟩
  rw [hn.1, BitVec.toNat_neg, BitVec.toNat_twoPow_of_lt hk, Nat.mod_eq_of_lt (by omega)]

private theorem sdiv_exact_pow2_neg {w : Nat} (x : Data.LLVM.Int w) (c : BitVec w)
    (h : Option.any (fun x => x.snd)
      (Option.map (fun x => (x, decide (c.toInt < 0))) (exactLog2? c.toInt.natAbs)) = true) :
    x.sdiv (.val c) true ⊒
      (Data.LLVM.Int.val 0#w).sub (x.ashr (shiftAmount w (.val (BitVec.ofNat w
        (Option.map (fun x => (x, decide (c.toInt < 0))) (exactLog2? c.toInt.natAbs)).get!.fst)))) := by
  cases hk : exactLog2? c.toInt.natAbs with
  | none => simp [hk] at h
  | some k =>
    simp only [hk, Option.map_some, Option.any_some, decide_eq_true_eq] at h
    simp only [Option.map_some, Option.get!_some]
    obtain ⟨hkw, rfl⟩ := eq_neg_twoPow_of_toInt ((slog2_some hk).1 h)
    rw [shiftAmount_ofNat hkw]
    veir_bv_normalize
    grind [BitVec.twoPow_eq_shiftLeft_one_ofInt_natCast, BitVec.lt_ofInt_natCast_ofNat_of_lt,
      BitVec.toNat_ofInt_natCast_of_lt, BitVec.sdiv_neg_one_shl_of_smod_eq_zero]

@[combine_valid, proof_manual]
theorem combine_sdiv_exact_by_pow2_neg_valid :
    Puddle.CTree.Pattern.Valid (sdiv_exact_by_pow2_pattern true) := by
  proveCombineValid using sdiv_exact_pow2_neg

private theorem shiftAmount_ofInt {w k : Nat} (hk : k < w) :
    shiftAmount w (Data.LLVM.Int.val (BitVec.ofInt w (k : Int))) = Data.LLVM.Int.constant w k := by
  rw [BitVec.ofInt_natCast]; exact shiftAmount_ofNat hk

/-- The shift amounts that `sdiv_by_pow2_pattern` creates are in range. -/
private theorem sdiv_shift_amounts {w k : Nat} (hk0 : 0 < k) (hkw : k < w) :
    shiftAmount w (Data.LLVM.Int.val (BitVec.ofInt w ((w : Int) - 1))) =
        Data.LLVM.Int.constant w (w - 1 : Nat) ∧
      shiftAmount w (Data.LLVM.Int.val (BitVec.ofInt w ((w : Int) - (k : Int)))) =
        Data.LLVM.Int.constant w (w - k : Nat) := by
  constructor
  · rw [show (w : Int) - 1 = ((w - 1 : Nat) : Int) by omega, shiftAmount_ofInt (by omega)]
  · rw [show (w : Int) - (k : Int) = ((w - k : Nat) : Int) by omega, shiftAmount_ofInt (by omega)]

private theorem sdiv_pow2_pos {w : Nat} (x : Data.LLVM.Int w) (c : BitVec w)
    (h : Option.any (fun x => !decide (x.fst = 0) && !x.snd)
      (Option.map (fun x => (x, decide (c.toInt < 0))) (exactLog2? c.toInt.natAbs)) = true) :
    x.sdiv (.val c) ⊒
      (x.add ((x.ashr (shiftAmount w (.val (BitVec.ofInt w ((w : Int) - 1))))).lshr
          (shiftAmount w (.val (BitVec.ofInt w ((w : Int) - ((Option.map
            (fun x => (x, decide (c.toInt < 0))) (exactLog2? c.toInt.natAbs)).get!.fst : Nat))))))).ashr
        (shiftAmount w (.val (BitVec.ofNat w
          (Option.map (fun x => (x, decide (c.toInt < 0))) (exactLog2? c.toInt.natAbs)).get!.fst))) := by
  cases hk : exactLog2? c.toInt.natAbs with
  | none => simp [hk] at h
  | some k =>
    simp only [hk, Option.map_some, Option.any_some, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not] at h
    simp only [Option.map_some, Option.get!_some]
    obtain ⟨hkw, rfl⟩ := eq_twoPow_of_toInt ((slog2_some hk).2 h.2)
    obtain ⟨h₁, h₂⟩ := sdiv_shift_amounts (Nat.pos_of_ne_zero h.1) (by omega : k < w)
    rw [h₁, h₂, shiftAmount_ofNat (by omega)]
    veir_bv_normalize
    grind [BitVec.twoPow_eq_shiftLeft_one_ofInt_natCast, BitVec.lt_ofInt_natCast_ofNat_of_lt,
      BitVec.toNat_ofInt_natCast_of_lt, BitVec.sdiv_one_shl_eq_biased_sshiftRight]

@[combine_valid, proof_manual]
theorem combine_sdiv_by_pow2_pos_valid :
    Puddle.CTree.Pattern.Valid (sdiv_by_pow2_pattern false) := by
  proveCombineValid using sdiv_pow2_pos

private theorem sdiv_pow2_neg {w : Nat} (x : Data.LLVM.Int w) (c : BitVec w)
    (h : Option.any (fun x => !decide (x.fst = 0) && x.snd)
      (Option.map (fun x => (x, decide (c.toInt < 0))) (exactLog2? c.toInt.natAbs)) = true) :
    x.sdiv (.val c) ⊒
      (Data.LLVM.Int.val 0#w).sub
        ((x.add ((x.ashr (shiftAmount w (.val (BitVec.ofInt w ((w : Int) - 1))))).lshr
          (shiftAmount w (.val (BitVec.ofInt w ((w : Int) - ((Option.map
            (fun x => (x, decide (c.toInt < 0))) (exactLog2? c.toInt.natAbs)).get!.fst : Nat))))))).ashr
        (shiftAmount w (.val (BitVec.ofNat w
          (Option.map (fun x => (x, decide (c.toInt < 0))) (exactLog2? c.toInt.natAbs)).get!.fst)))) := by
  cases hk : exactLog2? c.toInt.natAbs with
  | none => simp [hk] at h
  | some k =>
    simp only [hk, Option.map_some, Option.any_some, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, decide_eq_true_eq] at h
    simp only [Option.map_some, Option.get!_some]
    obtain ⟨hkw, rfl⟩ := eq_neg_twoPow_of_toInt ((slog2_some hk).1 h.2)
    obtain ⟨h₁, h₂⟩ := sdiv_shift_amounts (Nat.pos_of_ne_zero h.1) hkw
    rw [h₁, h₂, shiftAmount_ofNat hkw]
    veir_bv_normalize
    grind [BitVec.twoPow_eq_shiftLeft_one_ofInt_natCast, BitVec.lt_ofInt_natCast_ofNat_of_lt,
      BitVec.toNat_ofInt_natCast_of_lt, BitVec.sdiv_neg_one_shl_eq_neg_biased_sshiftRight]

@[combine_valid, proof_manual]
theorem combine_sdiv_by_pow2_neg_valid :
    Puddle.CTree.Pattern.Valid (sdiv_by_pow2_pattern true) := by
  proveCombineValid using sdiv_pow2_neg

open Veir.Data Veir.Data.LLVM in
/-- Prove the correctness of `mul_to_shl_pattern`: `x * 2^k` → `x << k`, whose flags carry over. A
multiplication that does not overflow makes the shift's no-wrap checks pass. -/
private theorem mul_twoPow_shl {w : Nat} (x : LLVM.Int w) (k : Nat) (hk : k + 1 < w) (n u : Bool) :
    x.mul (.val (BitVec.twoPow w k)) n u ⊒ x.shl (LLVM.Int.constant w k) n u := by
  have hkw : k < 2 ^ w := Nat.lt_trans (by omega) Nat.lt_two_pow_self
  have hlt : 2 ^ k < 2 ^ w := Nat.pow_lt_pow_right (by decide) (by omega)
  have hkn : (BitVec.ofInt w (k : _root_.Int)).toNat = k := by
    rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hkw]
  have hrange : ¬ (w : BitVec w) ≤ BitVec.ofInt w (k : _root_.Int) :=
    BitVec.not_le.mpr (BitVec.lt_ofInt_natCast_ofNat_of_lt (by omega))
  have hti : (BitVec.twoPow w k).toInt = 2 ^ k := by
    rw [BitVec.toInt_twoPow]
    simp only [show ¬ w ≤ k by omega, show ¬ k + 1 = w by omega, ite_false]
  cases x with
  | poison => simp [LLVM.Int.mul, Id.run, Data.LLVM.Int.poison_isRefinedBy]
  | val x =>
    have hv : x <<< BitVec.ofInt w (k : _root_.Int) = x * BitVec.twoPow w k := by
      rw [BitVec.shiftLeft_eq', hkn, BitVec.shiftLeft_eq_mul_twoPow]
    have hnuw (h : ¬ BitVec.umulOverflow x (BitVec.twoPow w k) = true) :
        x <<< BitVec.ofInt w (k : _root_.Int) >>> BitVec.ofInt w (k : _root_.Int) = x := by
      simp only [BitVec.umulOverflow, BitVec.toNat_twoPow_of_lt (by omega : k < w),
        decide_eq_true_eq, ge_iff_le, Nat.not_le] at h
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.ushiftRight_eq', hkn, hv, BitVec.toNat_ushiftRight, BitVec.toNat_mul,
        BitVec.toNat_twoPow_of_lt (by omega), Nat.mod_eq_of_lt h, Nat.shiftRight_eq_div_pow,
        Nat.mul_div_cancel _ (Nat.two_pow_pos k)]
    have hnsw (h : ¬ BitVec.smulOverflow x (BitVec.twoPow w k) = true) :
        (x <<< BitVec.ofInt w (k : _root_.Int)).sshiftRight' (BitVec.ofInt w (k : _root_.Int)) = x := by
      simp only [BitVec.smulOverflow, hti, Bool.or_eq_true, decide_eq_true_eq, not_or,
        ge_iff_le, _root_.Int.not_le, _root_.Int.not_lt] at h
      apply BitVec.eq_of_toInt_eq
      rw [BitVec.sshiftRight_eq', hkn, hv, BitVec.toInt_sshiftRight, BitVec.toInt_mul, hti,
        bmod_two_pow_of_range (by omega) h.2 h.1, _root_.Int.shiftRight_eq_div_pow]
      have hpos : (0 : _root_.Int) < 2 ^ k := by exact_mod_cast Nat.two_pow_pos k
      push_cast
      exact _root_.Int.mul_ediv_cancel _ (_root_.Int.ne_of_gt hpos)
    simp only [LLVM.Int.mul, LLVM.Int.shl, LLVM.Int.constant, Id.run, pure, ge_iff_le, hrange,
      ite_false]
    by_cases hs : n = true ∧ BitVec.smulOverflow x (BitVec.twoPow w k) = true
    · simp [hs, Data.LLVM.Int.poison_isRefinedBy]
    by_cases hu : u = true ∧ BitVec.umulOverflow x (BitVec.twoPow w k) = true
    · simp [hu, Data.LLVM.Int.poison_isRefinedBy]
    have hs' : ¬ (n = true ∧ (x <<< BitVec.ofInt w (k : _root_.Int)).sshiftRight'
        (BitVec.ofInt w (k : _root_.Int)) ≠ x) := by
      rintro ⟨hn, hne⟩; exact hne (hnsw fun h => hs ⟨hn, h⟩)
    have hu' : ¬ (u = true ∧ x <<< BitVec.ofInt w (k : _root_.Int) >>>
        BitVec.ofInt w (k : _root_.Int) ≠ x) := by
      rintro ⟨hn, hne⟩; exact hne (hnuw fun h => hu ⟨hn, h⟩)
    simp only [hs, hu, hs', hu', ite_false]
    rw [hv]
    exact Data.LLVM.Int.isRefinedBy_refl _

/-- The positive power of two `2^k` that `log2?` reads. -/
private theorem log2_some {w : Nat} {c : BitVec w}
    (h : (if 0 < c.toInt then exactLog2? c.toInt.toNat else none).isSome = true) :
    ∃ k, (if 0 < c.toInt then exactLog2? c.toInt.toNat else none) = some k ∧ k + 1 < w ∧
      c = BitVec.twoPow w k := by
  split at h
  · obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp h
    have habs := exactLog2?_eq_some hk
    have hP := two_pow_cast k
    have hci : c.toInt = 2 ^ k := by omega
    obtain ⟨hkw, hc⟩ := eq_twoPow_of_toInt hci
    exact ⟨k, by rw [ite_eq_left_of_eq_true _ _ (eq_true ‹_›)]; exact hk, hkw, hc⟩
  · simp at h

private theorem mul_pow2 {w : Nat} (x : Data.LLVM.Int w) (c : BitVec w)
    (h : (if 0 < c.toInt then exactLog2? c.toInt.toNat else none).isSome = true) (n u : Bool) :
    x.mul (.val c) n u ⊒
      x.shl (shiftAmount w (.val (BitVec.ofNat w
        (if 0 < c.toInt then exactLog2? c.toInt.toNat else none).get!))) n u := by
  obtain ⟨k, hk, hkw, rfl⟩ := log2_some h
  rw [hk, Option.get!_some, shiftAmount_ofNat (by omega)]
  exact mul_twoPow_shl x k hkw n u

@[combine_valid, proof_manual]
theorem combine_mul_to_shl_valid :
    Puddle.CTree.Pattern.Valid (mul_to_shl_pattern) := by
  proveCombineValid using mul_pow2

private theorem urem_pow2 {w : Nat} (x : Data.LLVM.Int w) (c : BitVec w)
    (h : (if 0 < c.toInt then exactLog2? c.toInt.toNat else none).isSome = true) :
    x.urem (.val c) ⊒ x.and (.val (BitVec.ofInt w (c.toInt - 1))) := by
  obtain ⟨k, -, hkw, rfl⟩ := log2_some h
  have hlt : 2 ^ k < 2 ^ w := Nat.pow_lt_pow_right (by decide) (by omega)
  have hne : BitVec.twoPow w k ≠ 0#w := by
    intro h0; have := congrArg BitVec.toNat h0
    simp [BitVec.toNat_twoPow_of_lt (by omega : k < w)] at this
  have hti : (BitVec.twoPow w k).toInt = 2 ^ k := by
    rw [BitVec.toInt_twoPow]
    simp only [show ¬ w ≤ k by omega, show ¬ k + 1 = w by omega, ite_false]
  have hmask : BitVec.ofInt w ((BitVec.twoPow w k).toInt - 1) = BitVec.ofNat w (2 ^ k - 1) := by
    have := Nat.one_le_two_pow (n := k)
    have hP := two_pow_cast k
    rw [hti, show (2 : Int) ^ k - 1 = ((2 ^ k - 1 : Nat) : Int) by omega, BitVec.ofInt_natCast]
  rw [hmask]
  cases x with
  | poison => simp [Data.LLVM.Int.urem, Id.run, Data.LLVM.Int.poison_isRefinedBy]
  | val x =>
    have hv : x % BitVec.twoPow w k = x &&& BitVec.ofNat w (2 ^ k - 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_umod, BitVec.toNat_and, BitVec.toNat_twoPow_of_lt (by omega),
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le (2 ^ k) 1) hlt),
        Nat.and_two_pow_sub_one_eq_mod]
    simp [Data.LLVM.Int.urem, Data.LLVM.Int.and, Id.run, hne, hv, Data.LLVM.Int.isRefinedBy_refl]

@[combine_valid, proof_manual]
theorem combine_urem_pow2_to_mask_valid :
    Puddle.CTree.Pattern.Valid (urem_pow2_to_mask_pattern) := by
  proveCombineValid using urem_pow2

/-! ### Constant folding -/

@[combine_valid, proof_pbv]
theorem combine_constant_fold_mul_valid :
    Puddle.CTree.Pattern.Valid (constant_fold_binop_pattern .g_mul ((· * ·))) := by
  proveCombineValid

/-! ### Selects of two constants -/

open Veir.Data Veir.Data.LLVM in
/--
Prove all four `redundant_and_select_pattern` arm combinations at every width, for any mask with
its low bit set. The hypotheses admit poison from a comparison, including on an unselected arm;
`zext_i1_eq_poison_or_zero_or_one` supplies them for widened comparisons.
-/
private theorem and_select_bool {w wc : Nat} (c : LLVM.Int wc) (t f : LLVM.Int w)
    (mask : BitVec w) (hmask : mask.toNat % 2 = 1)
    (ht : t = .poison ∨ t = .val 0#w ∨ t = .val 1#w)
    (hf : f = .poison ∨ f = .val 0#w ∨ f = .val 1#w) :
    LLVM.Int.and (GMIR.selectNonzero c t f) (.val mask) = GMIR.selectNonzero c t f := by
  have hone : 1#w &&& mask = 1#w := by
    apply BitVec.eq_of_toNat_eq
    cases w <;> simp_all
  cases c with
  | poison => simp [GMIR.selectNonzero, LLVM.Int.and, Id.run]
  | val c =>
    rcases ht with rfl | rfl | rfl <;> rcases hf with rfl | rfl | rfl <;>
      by_cases hc : c = 0#wc <;> simp [GMIR.selectNonzero, LLVM.Int.and, Id.run, hone, hc]

open Veir.Data Veir.Data.LLVM in
/-- `redundant_and_select_pattern`, whose mask `k` is odd as an integer, at every width. -/
private theorem and_select_bool_odd {w : Nat} {wc : Nat} (c : LLVM.Int wc) (t f : LLVM.Int w) (k : _root_.Int)
    (hk : k % 2 = 1)
    (ht : t = .poison ∨ t = .val 0#w ∨ t = .val 1#w)
    (hf : f = .poison ∨ f = .val 0#w ∨ f = .val 1#w) :
    LLVM.Int.and (GMIR.selectNonzero c t f) (.val (BitVec.ofInt w k)) ⊒ GMIR.selectNonzero c t f := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · generalize GMIR.selectNonzero c t f = r
    cases r <;> simp [LLVM.Int.and, Id.run, Data.LLVM.Int.poison_isRefinedBy, Data.LLVM.Int.isRefinedBy_refl,
      BitVec.of_length_zero]
  · rw [and_select_bool c t f _ _ ht hf]
    · exact Data.LLVM.Int.isRefinedBy_refl _
    · have hd : (2 : _root_.Int) ∣ ((2 ^ w : Nat) : _root_.Int) := by
        refine ⟨((2 ^ (w - 1) : Nat) : _root_.Int), ?_⟩
        rw [show w = (w - 1) + 1 by omega, Nat.pow_succ]
        push_cast
        rw [_root_.Int.mul_comm]
      have h0 : 0 ≤ k % ((2 ^ w : Nat) : _root_.Int) :=
        _root_.Int.emod_nonneg _ (by have := Nat.two_pow_pos w; omega)
      have h1 : (k % ((2 ^ w : Nat) : _root_.Int)) % 2 = 1 := by
        rw [_root_.Int.emod_emod_of_dvd _ hd]; exact hk
      simp only [BitVec.toNat_ofInt]
      omega

set_option maxHeartbeats 4000000 in
@[combine_valid, proof_manual]
theorem combine_redundant_and_select_icmp_constant_valid :
    Puddle.CTree.Pattern.Valid (redundant_and_select_pattern .icmp .constant) := by
  proveCombineValid using and_select_bool_odd

set_option maxHeartbeats 4000000 in
@[combine_valid, proof_manual]
theorem combine_redundant_and_select_constant_icmp_valid :
    Puddle.CTree.Pattern.Valid (redundant_and_select_pattern .constant .icmp) := by
  proveCombineValid using and_select_bool_odd

set_option maxHeartbeats 4000000 in
@[combine_valid, proof_manual]
theorem combine_redundant_and_select_constant_constant_valid :
    Puddle.CTree.Pattern.Valid (redundant_and_select_pattern .constant .constant) := by
  proveCombineValid using and_select_bool_odd

open Veir.Data Veir.Data.LLVM in
/-- A property of `GMIR.selectNonzero` on an `i1` condition follows from its three cases. -/
private theorem selectNonzero_refines {w : Nat} (c : LLVM.Int 1) (x y : LLVM.Int w)
    (r : LLVM.Int w)
    (hp : c = .poison → r = .poison)
    (h1 : c = .val 1#1 → x ⊒ r) (h0 : c = .val 0#1 → y ⊒ r) :
    GMIR.selectNonzero c x y ⊒ r := by
  cases c with
  | poison => simp [GMIR.selectNonzero, Id.run, hp, LLVM.Int.isRefinedBy]
  | val c =>
    rcases BitVec.eq_zero_or_eq_one c with rfl | rfl
    · simpa [GMIR.selectNonzero, Id.run] using h0 rfl
    · simpa [GMIR.selectNonzero, Id.run] using h1 rfl

/-- Closes one case of a `tryFoldSelectOfConstants` proof, where the condition is known. -/
macro "select_const_tac" : tactic =>
  `(tactic| (simp_all [Veir.Data.LLVM.notI1, Nat.not_le_of_gt, Nat.mod_eq_of_lt,
      BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt, BitVec.signExtend, BitVec.ofInt_neg,
      BitVec.twoPow_eq, BitVec.add_comm, BitVec.sub_eq_add_neg, BitVec.neg_one_eq_allOnes,
      Veir.Data.LLVM.Int.xor, Veir.Data.LLVM.Int.zext, Veir.Data.LLVM.Int.sext, Veir.Data.LLVM.Int.add, Veir.Data.LLVM.Int.shl, Veir.Data.LLVM.Int.or,
      Veir.Data.LLVM.Int.constant, Id.run, Veir.Data.LLVM.Int.isRefinedBy]))

open Veir.Data Veir.Data.LLVM in
/-- Prove the correctness of combining `c ? 2^k : 0` to `shl (zext c), k`. -/
private theorem select_pow2_zero {w : Nat} (h : 1 < w) (c : LLVM.Int 1) (k : Nat) (hk : k < w) :
    GMIR.selectNonzero c (LLVM.Int.val (BitVec.twoPow w k)) (LLVM.Int.constant w 0) ⊒
      LLVM.Int.shl (LLVM.Int.zext c w false h) (LLVM.Int.constant w k) := by
  have hkpow := Nat.lt_trans hk Nat.lt_two_pow_self
  apply selectNonzero_refines <;> rintro rfl <;> select_const_tac

private theorem constant_eq {w : Nat} (v : Int) :
    Data.LLVM.Int.constant w v = .val (BitVec.ofInt w v) := rfl

/-- The constant `2^k` that `ulog2?` reads. -/
private theorem ulog2_some {w : Nat} {t : BitVec w} (h : (exactLog2? t.toNat).isSome = true) :
    ∃ k, exactLog2? t.toNat = some k ∧ k < w ∧ t = BitVec.twoPow w k := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp h
  have hc2 := exactLog2?_eq_some hk
  have hkw : k < w := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (hc2 ▸ t.isLt)
  exact ⟨k, hk, hkw, BitVec.eq_of_toNat_eq (by rw [hc2, BitVec.toNat_twoPow_of_lt hkw])⟩

private theorem soc_pow2_zero {w : Nat} (h : 1 < w) (_hw : w ≤ 64) (c : Data.LLVM.Int 1)
    (t f : BitVec w) (ht : (exactLog2? t.toNat).isSome = true) (hf : f = 0) :
    GMIR.selectNonzero c (.val t) (.val f) ⊒
      (c.zext w false h).shl (shiftAmount w (.val (BitVec.ofNat w (exactLog2? t.toNat).get!))) := by
  obtain ⟨k, hk, hkw, rfl⟩ := ulog2_some ht
  subst hf
  rw [hk, Option.get!_some, shiftAmount_ofNat hkw]
  simpa [constant_eq] using select_pow2_zero h c k hkw

@[combine_valid, proof_manual]
theorem combine_select_pow2_zero_valid :
    Puddle.CTree.Pattern.Valid (select_pow2_zero_pattern) := by
  proveCombineValid using soc_pow2_zero

open Veir.Data Veir.Data.LLVM in
/-- Prove the correctness of combining `c ? 0 : 2^k` to `shl (zext (not c)), k`. -/
private theorem select_zero_pow2 {w : Nat} (h : 1 < w) (c : LLVM.Int 1) (k : Nat) (hk : k < w) :
    GMIR.selectNonzero c (LLVM.Int.constant w 0) (LLVM.Int.val (BitVec.twoPow w k)) ⊒
      LLVM.Int.shl (LLVM.Int.zext (notI1 c) w false h) (LLVM.Int.constant w k) := by
  have hkpow := Nat.lt_trans hk Nat.lt_two_pow_self
  apply selectNonzero_refines <;> rintro rfl <;> select_const_tac

private theorem ofInt_one_neg_one : BitVec.ofInt 1 (-1) = 1#1 := by decide

private theorem notI1_eq (c : Data.LLVM.Int 1) : Data.LLVM.notI1 c = c.xor (.val 1#1) := by
  simp [Data.LLVM.notI1, constant_eq, ofInt_one_neg_one]

private theorem soc_zero_pow2 {w : Nat} (h : 1 < w) (_hw : w ≤ 64) (c : Data.LLVM.Int 1)
    (t f : BitVec w) (hf : (exactLog2? f.toNat).isSome = true) (ht : t = 0) :
    GMIR.selectNonzero c (.val t) (.val f) ⊒
      ((c.xor (.val 1#1)).zext w false h).shl
        (shiftAmount w (.val (BitVec.ofNat w (exactLog2? f.toNat).get!))) := by
  obtain ⟨k, hk, hkw, rfl⟩ := ulog2_some hf
  subst ht
  rw [hk, Option.get!_some, shiftAmount_ofNat hkw]
  simpa [constant_eq, notI1_eq] using select_zero_pow2 h c k hkw

@[combine_valid, proof_manual]
theorem combine_select_zero_pow2_valid :
    Puddle.CTree.Pattern.Valid (select_zero_pow2_pattern) := by
  proveCombineValid using soc_zero_pow2

/-! ### Funnel shifts by a constant -/

private theorem fshr_zero {w v : Nat} (x y : Data.LLVM.Int w) (c : BitVec v) (hc : c = 0) :
    x.fshr y (GMIR.funnelShiftAmount w (.val c)) ⊒ y := by
  subst hc
  cases x <;> cases y <;> simp [Data.LLVM.Int.fshr, GMIR.funnelShiftAmount, Id.run, Data.LLVM.Int.poison_isRefinedBy]
  ext i hi; simp [hi, BitVec.getLsbD_append]

set_option maxHeartbeats 4000000 in
@[combine_valid, proof_manual]
theorem combine_funnel_shift_right_zero_valid :
    Puddle.CTree.Pattern.Valid (funnel_shift_zero_pattern .g_fshr true) := by
  /- The types are `TypeAttr`s: split each, so that the type of the constant, which
  `matchConstant` equates, substitutes, and normalize again. -/
  proveCombineValid with
    (casesLocalsOf Subtype)
    all_goals (try subst_vars)
    all_goals (try simp_all)
    normalizeLegalValid
    all_goals closeConstWith fshr_zero

private theorem fshl_zero {w v : Nat} (x y : Data.LLVM.Int w) (c : BitVec v) (hc : c = 0) :
    x.fshl y (GMIR.funnelShiftAmount w (.val c)) ⊒ x := by
  subst hc
  cases x <;> cases y <;> simp [Data.LLVM.Int.fshl, GMIR.funnelShiftAmount, Id.run, Data.LLVM.Int.poison_isRefinedBy]
  ext i hi; simp [hi, BitVec.getLsbD_append, BitVec.getElem_extractLsb', BitVec.getElem_append,
    show ¬ w + i < w by omega]

set_option maxHeartbeats 4000000 in
@[combine_valid, proof_manual]
theorem combine_funnel_shift_left_zero_valid :
    Puddle.CTree.Pattern.Valid (funnel_shift_zero_pattern .g_fshl false) := by
  /- The types are `TypeAttr`s: split each, so that the type of the constant, which
  `matchConstant` equates, substitutes, and normalize again. -/
  proveCombineValid with
    (casesLocalsOf Subtype)
    all_goals (try subst_vars)
    all_goals (try simp_all)
    normalizeLegalValid
    all_goals closeConstWith fshl_zero

/-- The matcher of `funnel_shift_overshift_pattern` only accepts an integer result type. -/
private theorem overshiftAmount?_isSome {p : GMIRConstantProperties} {attr : Attribute}
    {h : attr.isType = true} (hs : (overshiftAmount? p ⟨attr, h⟩).isSome = true) :
    ∃ t, attr = .integerType t := by
  cases attr <;> simp [overshiftAmount?] at hs ⊢ <;> exact ⟨_, rfl⟩

/-- `overshiftAmount?` at an integer result type. -/
private theorem overshiftAmount?_integerType (v : Int) (t' t : IntegerType)
    (h : (Attribute.integerType t).isType = true) :
    overshiftAmount? ⟨⟨v, t'⟩⟩ ⟨.integerType t, h⟩ =
      if (BitVec.ofInt t'.bitwidth v).toNat < t.bitwidth then none
      else some ⟨IntegerAttr.ofInt (((BitVec.ofInt t'.bitwidth v).toNat % t.bitwidth : Nat) : Int) t'⟩ := by
  by_cases hc : (BitVec.ofInt t'.bitwidth v).toNat < t.bitwidth <;>
    simp only [overshiftAmount?, GMIRConstantProperties.bits, hc, ite_true, ite_false] <;> rfl

/-- The amount `C % w` that replaces an over-large constant amount `C`: the funnel shift takes its
amount modulo `w` anyway. -/
private theorem funnelShiftAmount_overshift {w v : Nat} (c : BitVec v) (s : IntegerType.Signedness) :
    GMIR.funnelShiftAmount w
        (Data.LLVM.Int.val (BitVec.ofInt v (IntegerAttr.ofInt ((c.toNat % w : Nat) : Int) ⟨v, s⟩).value)) =
      GMIR.funnelShiftAmount w (.val c) := by
  rw [ofInt_ofInt_value, BitVec.ofInt_natCast]
  simp only [GMIR.funnelShiftAmount, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) c.isLt), Nat.mod_mod]

/-- `funnelShiftAmount_overshift`, in the normal form of `simp`. -/
private theorem funnelShiftAmount_overshift' {w v : Nat} (x : Int) (s : IntegerType.Signedness) :
    GMIR.funnelShiftAmount w
        (Data.LLVM.Int.val (BitVec.ofInt v (IntegerAttr.ofInt (max (x % 2 ^ v) 0 % (w : Int)) ⟨v, s⟩).value)) =
      GMIR.funnelShiftAmount w (.val (BitVec.ofInt v x)) := by
  have := funnelShiftAmount_overshift (w := w) (BitVec.ofInt v x) s
  simpa using this

set_option maxHeartbeats 4000000 in
@[combine_valid, proof_manual]
theorem combine_funnel_shift_overshift_l_valid :
    Puddle.CTree.Pattern.Valid (funnel_shift_overshift_pattern .g_fshl) := by
  simpCombineSemantics
  /- The created `g_constant` reads its type `amtType` as an integer or a pointer type: substitute
  the integer type the matched constant gives it before `simp_all` rewrites with that equation. -/
  intros
  all_goals (casesLocalsOf Subtype)
  all_goals (try dsimp only at *)
  all_goals (try subst_vars)
  normalizeLegalValid
  normalizeConstants
  all_goals (casesLocalsOf Subtype)
  all_goals (try subst_vars)
  all_goals (try simp_all)
  normalizeLegalValid
  all_goals (obtain ⟨t, rfl⟩ := overshiftAmount?_isSome ‹_›)
  all_goals (simp only [RuntimeValue.Conforms] at *)
  all_goals subst_vars
  all_goals (simp only [overshiftAmount?_integerType] at *)
  all_goals split
  all_goals (try simp_all [funnelShiftAmount_overshift', RuntimeValue.isRefinedBy, Data.LLVM.Int.isRefinedBy_refl])
  all_goals (rename_i heq; subst heq)
  all_goals (simp only [funnelShiftAmount_overshift']; exact Data.LLVM.Int.isRefinedBy_refl _)

set_option maxHeartbeats 4000000 in
@[combine_valid, proof_manual]
theorem combine_funnel_shift_overshift_r_valid :
    Puddle.CTree.Pattern.Valid (funnel_shift_overshift_pattern .g_fshr) := by
  simpCombineSemantics
  /- The created `g_constant` reads its type `amtType` as an integer or a pointer type: substitute
  the integer type the matched constant gives it before `simp_all` rewrites with that equation. -/
  intros
  all_goals (casesLocalsOf Subtype)
  all_goals (try dsimp only at *)
  all_goals (try subst_vars)
  normalizeLegalValid
  normalizeConstants
  all_goals (casesLocalsOf Subtype)
  all_goals (try subst_vars)
  all_goals (try simp_all)
  normalizeLegalValid
  all_goals (obtain ⟨t, rfl⟩ := overshiftAmount?_isSome ‹_›)
  all_goals (simp only [RuntimeValue.Conforms] at *)
  all_goals subst_vars
  all_goals (simp only [overshiftAmount?_integerType] at *)
  all_goals split
  all_goals (try simp_all [funnelShiftAmount_overshift', RuntimeValue.isRefinedBy, Data.LLVM.Int.isRefinedBy_refl])
  all_goals (rename_i heq; subst heq)
  all_goals (simp only [funnelShiftAmount_overshift']; exact Data.LLVM.Int.isRefinedBy_refl _)

/-! ## Status of every combine that matches a constant -/

@[legalization_status]
theorem combine_right_identity_one_int_status :
    Status Unproven (right_identity_one_int_pattern) :=
  .proven (combine_right_identity_one_int_valid)

@[legalization_status]
theorem combine_sub_one_from_sub_status :
    Status Unproven (sub_one_from_sub_pattern) :=
  .proven (combine_sub_one_from_sub_valid)

@[legalization_status]
theorem combine_sub_of_mul_const_status :
    Status Unproven (sub_of_mul_const_pattern) :=
  .proven (combine_sub_of_mul_const_valid)

@[legalization_status]
theorem combine_mul_by_neg_one_status :
    Status Unproven (mul_by_neg_one_pattern) :=
  .proven (combine_mul_by_neg_one_valid)

@[legalization_status]
theorem combine_mulo_by_2_status :
    Status Unproven (mulo_by_2_pattern) :=
  .proven (combine_mulo_by_2_valid)

@[legalization_status]
theorem combine_not_cmp_fold_eq_status :
    Status Unproven (not_cmp_fold_pattern .eq .ne) :=
  .proven (combine_not_cmp_fold_eq_valid)

@[legalization_status]
theorem combine_not_cmp_fold_ne_status :
    Status Unproven (not_cmp_fold_pattern .ne .eq) :=
  .proven (combine_not_cmp_fold_ne_valid)

@[legalization_status]
theorem combine_not_cmp_fold_ugt_status :
    Status Unproven (not_cmp_fold_pattern .ugt .ule) :=
  .proven (combine_not_cmp_fold_ugt_valid)

@[legalization_status]
theorem combine_not_cmp_fold_uge_status :
    Status Unproven (not_cmp_fold_pattern .uge .ult) :=
  .proven (combine_not_cmp_fold_uge_valid)

@[legalization_status]
theorem combine_not_cmp_fold_ult_status :
    Status Unproven (not_cmp_fold_pattern .ult .uge) :=
  .proven (combine_not_cmp_fold_ult_valid)

@[legalization_status]
theorem combine_not_cmp_fold_ule_status :
    Status Unproven (not_cmp_fold_pattern .ule .ugt) :=
  .proven (combine_not_cmp_fold_ule_valid)

@[legalization_status]
theorem combine_not_cmp_fold_sgt_status :
    Status Unproven (not_cmp_fold_pattern .sgt .sle) :=
  .proven (combine_not_cmp_fold_sgt_valid)

@[legalization_status]
theorem combine_not_cmp_fold_sge_status :
    Status Unproven (not_cmp_fold_pattern .sge .slt) :=
  .proven (combine_not_cmp_fold_sge_valid)

@[legalization_status]
theorem combine_not_cmp_fold_slt_status :
    Status Unproven (not_cmp_fold_pattern .slt .sge) :=
  .proven (combine_not_cmp_fold_slt_valid)

@[legalization_status]
theorem combine_not_cmp_fold_sle_status :
    Status Unproven (not_cmp_fold_pattern .sle .sgt) :=
  .proven (combine_not_cmp_fold_sle_valid)

@[legalization_status]
theorem combine_udiv_by_pow2_status :
    Status Unproven (udiv_by_pow2_pattern) :=
  .proven (combine_udiv_by_pow2_valid)

@[legalization_status]
theorem combine_sdiv_exact_by_pow2_pos_status :
    Status Unproven (sdiv_exact_by_pow2_pattern false) :=
  .proven (combine_sdiv_exact_by_pow2_pos_valid)

@[legalization_status]
theorem combine_sdiv_exact_by_pow2_neg_status :
    Status Unproven (sdiv_exact_by_pow2_pattern true) :=
  .proven (combine_sdiv_exact_by_pow2_neg_valid)

@[legalization_status]
theorem combine_sdiv_by_pow2_pos_status :
    Status Unproven (sdiv_by_pow2_pattern false) :=
  .proven (combine_sdiv_by_pow2_pos_valid)

@[legalization_status]
theorem combine_sdiv_by_pow2_neg_status :
    Status Unproven (sdiv_by_pow2_pattern true) :=
  .proven (combine_sdiv_by_pow2_neg_valid)

@[legalization_status]
theorem combine_mul_to_shl_status :
    Status Unproven (mul_to_shl_pattern) :=
  .proven (combine_mul_to_shl_valid)

@[legalization_status]
theorem combine_urem_pow2_to_mask_status :
    Status Unproven (urem_pow2_to_mask_pattern) :=
  .proven (combine_urem_pow2_to_mask_valid)

@[legalization_status]
theorem combine_constant_fold_mul_status :
    Status Unproven (constant_fold_binop_pattern .g_mul ((· * ·))) :=
  .proven (combine_constant_fold_mul_valid)

@[legalization_status]
theorem combine_redundant_and_select_icmp_constant_status :
    Status Unproven (redundant_and_select_pattern .icmp .constant) :=
  .proven (combine_redundant_and_select_icmp_constant_valid)

@[legalization_status]
theorem combine_redundant_and_select_constant_icmp_status :
    Status Unproven (redundant_and_select_pattern .constant .icmp) :=
  .proven (combine_redundant_and_select_constant_icmp_valid)

@[legalization_status]
theorem combine_redundant_and_select_constant_constant_status :
    Status Unproven (redundant_and_select_pattern .constant .constant) :=
  .proven (combine_redundant_and_select_constant_constant_valid)

@[legalization_status]
theorem combine_select_pow2_zero_status :
    Status Unproven (select_pow2_zero_pattern) :=
  .proven (combine_select_pow2_zero_valid)

@[legalization_status]
theorem combine_select_zero_pow2_status :
    Status Unproven (select_zero_pow2_pattern) :=
  .proven (combine_select_zero_pow2_valid)

@[legalization_status]
theorem combine_funnel_shift_right_zero_status :
    Status Unproven (funnel_shift_zero_pattern .g_fshr true) :=
  .proven (combine_funnel_shift_right_zero_valid)

@[legalization_status]
theorem combine_funnel_shift_left_zero_status :
    Status Unproven (funnel_shift_zero_pattern .g_fshl false) :=
  .proven (combine_funnel_shift_left_zero_valid)

@[legalization_status]
theorem combine_funnel_shift_overshift_l_status :
    Status Unproven (funnel_shift_overshift_pattern .g_fshl) :=
  .proven (combine_funnel_shift_overshift_l_valid)

@[legalization_status]
theorem combine_funnel_shift_overshift_r_status :
    Status Unproven (funnel_shift_overshift_pattern .g_fshr) :=
  .proven (combine_funnel_shift_overshift_r_valid)

/-! ## Combines decided by `pbv_decide`

Each combine is proven by `proveCombineValid` alone: the matchers bound every integer width by 64,
which discharges the side goals `w ≤ 64` of `pbv_decide`. The combines `pbv_decide` does not prove
are commented out, with the reason it fails. -/

@[combine_valid, proof_pbv]
theorem combine_hoist_and_shl_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_and .g_shl) := by
  proveCombineValid

@[legalization_status]
theorem combine_hoist_and_shl_status :
    Status Unproven (hoist_logic_op_pattern .g_and .g_shl) :=
  .proven (combine_hoist_and_shl_valid )

@[combine_valid, proof_pbv]
theorem combine_hoist_and_lshr_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_and .g_lshr) := by
  proveCombineValid

@[legalization_status]
theorem combine_hoist_and_lshr_status :
    Status Unproven (hoist_logic_op_pattern .g_and .g_lshr) :=
  .proven (combine_hoist_and_lshr_valid )

@[combine_valid, proof_pbv]
theorem combine_hoist_and_ashr_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_and .g_ashr) := by
  proveCombineValid

@[legalization_status]
theorem combine_hoist_and_ashr_status :
    Status Unproven (hoist_logic_op_pattern .g_and .g_ashr) :=
  .proven (combine_hoist_and_ashr_valid )

@[combine_valid, proof_pbv]
theorem combine_hoist_and_and_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_and .g_and) := by
  proveCombineValid

@[legalization_status]
theorem combine_hoist_and_and_status :
    Status Unproven (hoist_logic_op_pattern .g_and .g_and) :=
  .proven (combine_hoist_and_and_valid )

@[combine_valid, proof_pbv]
theorem combine_hoist_or_shl_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_or .g_shl) := by
  proveCombineValid

@[legalization_status]
theorem combine_hoist_or_shl_status :
    Status Unproven (hoist_logic_op_pattern .g_or .g_shl) :=
  .proven (combine_hoist_or_shl_valid )

@[combine_valid, proof_pbv]
theorem combine_hoist_or_lshr_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_or .g_lshr) := by
  proveCombineValid

@[legalization_status]
theorem combine_hoist_or_lshr_status :
    Status Unproven (hoist_logic_op_pattern .g_or .g_lshr) :=
  .proven (combine_hoist_or_lshr_valid )

@[combine_valid, proof_pbv]
theorem combine_hoist_or_ashr_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_or .g_ashr) := by
  proveCombineValid

@[legalization_status]
theorem combine_hoist_or_ashr_status :
    Status Unproven (hoist_logic_op_pattern .g_or .g_ashr) :=
  .proven (combine_hoist_or_ashr_valid )

@[combine_valid, proof_pbv]
theorem combine_hoist_or_and_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_or .g_and) := by
  proveCombineValid

@[legalization_status]
theorem combine_hoist_or_and_status :
    Status Unproven (hoist_logic_op_pattern .g_or .g_and) :=
  .proven (combine_hoist_or_and_valid )

@[combine_valid, proof_pbv]
theorem combine_hoist_xor_shl_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_xor .g_shl) := by
  proveCombineValid

@[legalization_status]
theorem combine_hoist_xor_shl_status :
    Status Unproven (hoist_logic_op_pattern .g_xor .g_shl) :=
  .proven (combine_hoist_xor_shl_valid )

@[combine_valid, proof_pbv]
theorem combine_hoist_xor_lshr_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_xor .g_lshr) := by
  proveCombineValid

@[legalization_status]
theorem combine_hoist_xor_lshr_status :
    Status Unproven (hoist_logic_op_pattern .g_xor .g_lshr) :=
  .proven (combine_hoist_xor_lshr_valid )

@[combine_valid, proof_pbv]
theorem combine_hoist_xor_ashr_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_xor .g_ashr) := by
  proveCombineValid

@[legalization_status]
theorem combine_hoist_xor_ashr_status :
    Status Unproven (hoist_logic_op_pattern .g_xor .g_ashr) :=
  .proven (combine_hoist_xor_ashr_valid )

@[combine_valid, proof_pbv]
theorem combine_hoist_xor_and_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_xor .g_and) := by
  proveCombineValid

@[legalization_status]
theorem combine_hoist_xor_and_status :
    Status Unproven (hoist_logic_op_pattern .g_xor .g_and) :=
  .proven (combine_hoist_xor_and_valid )

@[combine_valid, proof_pbv]
theorem combine_sub_add_reg_x_add_y_sub_y_valid : Puddle.CTree.Pattern.Valid sub_add_reg_x_add_y_sub_y_pattern := by
  proveCombineValid

@[legalization_status]
theorem combine_sub_add_reg_x_add_y_sub_y_status :
    Status Unproven sub_add_reg_x_add_y_sub_y_pattern :=
  .proven (combine_sub_add_reg_x_add_y_sub_y_valid )

@[combine_valid, proof_pbv]
theorem combine_sub_add_reg_x_add_y_sub_x_valid : Puddle.CTree.Pattern.Valid sub_add_reg_x_add_y_sub_x_pattern := by
  proveCombineValid

@[legalization_status]
theorem combine_sub_add_reg_x_add_y_sub_x_status :
    Status Unproven sub_add_reg_x_add_y_sub_x_pattern :=
  .proven (combine_sub_add_reg_x_add_y_sub_x_valid )

@[combine_valid, proof_pbv]
theorem combine_sub_add_reg_negate_valid : Puddle.CTree.Pattern.Valid (sub_add_reg_negate_pattern false) := by
  proveCombineValid

@[legalization_status]
theorem combine_sub_add_reg_negate_status :
    Status Unproven (sub_add_reg_negate_pattern false) :=
  .proven (combine_sub_add_reg_negate_valid )

@[combine_valid, proof_pbv]
theorem combine_sub_add_reg_negate_x_first_valid : Puddle.CTree.Pattern.Valid (sub_add_reg_negate_pattern true) := by
  proveCombineValid

@[legalization_status]
theorem combine_sub_add_reg_negate_x_first_status :
    Status Unproven (sub_add_reg_negate_pattern true) :=
  .proven (combine_sub_add_reg_negate_x_first_valid )

@[combine_valid, proof_pbv]
theorem combine_xor_of_and_with_same_reg_valid : Puddle.CTree.Pattern.Valid xor_of_and_with_same_reg_pattern := by
  proveCombineValid

@[legalization_status]
theorem combine_xor_of_and_with_same_reg_status :
    Status Unproven xor_of_and_with_same_reg_pattern :=
  .proven (combine_xor_of_and_with_same_reg_valid )

@[combine_valid, proof_pbv]
theorem combine_trunc_of_zext_valid : Puddle.CTree.Pattern.Valid (trunc_of_ext_pattern .g_zext) := by
  proveCombineValid

@[legalization_status]
theorem combine_trunc_of_zext_status :
    Status Unproven (trunc_of_ext_pattern .g_zext) :=
  .proven (combine_trunc_of_zext_valid )

@[combine_valid, proof_pbv]
theorem combine_trunc_of_sext_valid : Puddle.CTree.Pattern.Valid (trunc_of_ext_pattern .g_sext) := by
  proveCombineValid

@[legalization_status]
theorem combine_trunc_of_sext_status :
    Status Unproven (trunc_of_ext_pattern .g_sext) :=
  .proven (combine_trunc_of_sext_valid )

@[combine_valid, proof_pbv]
theorem combine_redundant_add_eq_valid : Puddle.CTree.Pattern.Valid (redundant_binop_in_equality_pattern .g_add .eq) := by
  proveCombineValid

@[legalization_status]
theorem combine_redundant_add_eq_status :
    Status Unproven (redundant_binop_in_equality_pattern .g_add .eq) :=
  .proven (combine_redundant_add_eq_valid )

@[combine_valid, proof_pbv]
theorem combine_redundant_add_ne_valid : Puddle.CTree.Pattern.Valid (redundant_binop_in_equality_pattern .g_add .ne) := by
  proveCombineValid

@[legalization_status]
theorem combine_redundant_add_ne_status :
    Status Unproven (redundant_binop_in_equality_pattern .g_add .ne) :=
  .proven (combine_redundant_add_ne_valid )

@[combine_valid, proof_pbv]
theorem combine_redundant_sub_eq_valid : Puddle.CTree.Pattern.Valid (redundant_binop_in_equality_pattern .g_sub .eq) := by
  proveCombineValid

@[legalization_status]
theorem combine_redundant_sub_eq_status :
    Status Unproven (redundant_binop_in_equality_pattern .g_sub .eq) :=
  .proven (combine_redundant_sub_eq_valid )

@[combine_valid, proof_pbv]
theorem combine_redundant_sub_ne_valid : Puddle.CTree.Pattern.Valid (redundant_binop_in_equality_pattern .g_sub .ne) := by
  proveCombineValid

@[legalization_status]
theorem combine_redundant_sub_ne_status :
    Status Unproven (redundant_binop_in_equality_pattern .g_sub .ne) :=
  .proven (combine_redundant_sub_ne_valid )

@[combine_valid, proof_pbv]
theorem combine_redundant_xor_eq_valid : Puddle.CTree.Pattern.Valid (redundant_binop_in_equality_pattern .g_xor .eq) := by
  proveCombineValid

@[legalization_status]
theorem combine_redundant_xor_eq_status :
    Status Unproven (redundant_binop_in_equality_pattern .g_xor .eq) :=
  .proven (combine_redundant_xor_eq_valid )

@[combine_valid, proof_pbv]
theorem combine_redundant_xor_ne_valid : Puddle.CTree.Pattern.Valid (redundant_binop_in_equality_pattern .g_xor .ne) := by
  proveCombineValid

@[legalization_status]
theorem combine_redundant_xor_ne_status :
    Status Unproven (redundant_binop_in_equality_pattern .g_xor .ne) :=
  .proven (combine_redundant_xor_ne_valid )

@[combine_valid, proof_pbv]
theorem combine_combine_or_of_and_tt_valid : Puddle.CTree.Pattern.Valid (combine_or_of_and_pattern true true) := by
  proveCombineValid

@[legalization_status]
theorem combine_combine_or_of_and_tt_status :
    Status Unproven (combine_or_of_and_pattern true true) :=
  .proven (combine_combine_or_of_and_tt_valid )

@[combine_valid, proof_pbv]
theorem combine_combine_or_of_and_tf_valid : Puddle.CTree.Pattern.Valid (combine_or_of_and_pattern true false) := by
  proveCombineValid

@[legalization_status]
theorem combine_combine_or_of_and_tf_status :
    Status Unproven (combine_or_of_and_pattern true false) :=
  .proven (combine_combine_or_of_and_tf_valid )

@[combine_valid, proof_pbv]
theorem combine_combine_or_of_and_ft_valid : Puddle.CTree.Pattern.Valid (combine_or_of_and_pattern false true) := by
  proveCombineValid

@[legalization_status]
theorem combine_combine_or_of_and_ft_status :
    Status Unproven (combine_or_of_and_pattern false true) :=
  .proven (combine_combine_or_of_and_ft_valid )

@[combine_valid, proof_pbv]
theorem combine_combine_or_of_and_ff_valid : Puddle.CTree.Pattern.Valid (combine_or_of_and_pattern false false) := by
  proveCombineValid

@[legalization_status]
theorem combine_combine_or_of_and_ff_status :
    Status Unproven (combine_or_of_and_pattern false false) :=
  .proven (combine_combine_or_of_and_ff_valid )

@[combine_valid, proof_pbv]
theorem combine_AMinusBMinusC_valid : Puddle.CTree.Pattern.Valid AMinusBMinusC_pattern := by
  proveCombineValid

@[legalization_status]
theorem combine_AMinusBMinusC_status :
    Status Unproven AMinusBMinusC_pattern :=
  .proven (combine_AMinusBMinusC_valid )

@[combine_valid, proof_pbv]
theorem combine_zext_of_zext_valid : Puddle.CTree.Pattern.Valid (ext_of_ext_pattern .g_zext) := by
  proveCombineValid

@[legalization_status]
theorem combine_zext_of_zext_status :
    Status Unproven (ext_of_ext_pattern .g_zext) :=
  .proven (combine_zext_of_zext_valid )

@[combine_valid, proof_pbv]
theorem combine_sext_of_sext_valid : Puddle.CTree.Pattern.Valid (ext_of_ext_pattern .g_sext) := by
  proveCombineValid

@[legalization_status]
theorem combine_sext_of_sext_status :
    Status Unproven (ext_of_ext_pattern .g_sext) :=
  .proven (combine_sext_of_sext_valid )

@[combine_valid, proof_pbv]
theorem combine_bitreverse_shl_valid : Puddle.CTree.Pattern.Valid (bitreverse_shift_pattern .g_shl .g_lshr) := by
  proveCombineValid

@[legalization_status]
theorem combine_bitreverse_shl_status :
    Status Unproven (bitreverse_shift_pattern .g_shl .g_lshr) :=
  .proven (combine_bitreverse_shl_valid )

@[combine_valid, proof_pbv]
theorem combine_bitreverse_lshr_valid : Puddle.CTree.Pattern.Valid (bitreverse_shift_pattern .g_lshr .g_shl) := by
  proveCombineValid

@[legalization_status]
theorem combine_bitreverse_lshr_status :
    Status Unproven (bitreverse_shift_pattern .g_lshr .g_shl) :=
  .proven (combine_bitreverse_lshr_valid )

@[combine_valid, proof_pbv]
theorem combine_binop_same_val_and_valid : Puddle.CTree.Pattern.Valid (binop_same_val_pattern .g_and) := by
  proveCombineValid

@[legalization_status]
theorem combine_binop_same_val_and_status :
    Status Unproven (binop_same_val_pattern .g_and) :=
  .proven (combine_binop_same_val_and_valid )

@[combine_valid, proof_pbv]
theorem combine_binop_same_val_or_valid : Puddle.CTree.Pattern.Valid (binop_same_val_pattern .g_or) := by
  proveCombineValid

@[legalization_status]
theorem combine_binop_same_val_or_status :
    Status Unproven (binop_same_val_pattern .g_or) :=
  .proven (combine_binop_same_val_or_valid )

@[combine_valid, proof_pbv]
theorem combine_same_val_zero_sub_valid : Puddle.CTree.Pattern.Valid (same_val_zero_pattern .g_sub) := by
  proveCombineValid

@[legalization_status]
theorem combine_same_val_zero_sub_status :
    Status Unproven (same_val_zero_pattern .g_sub) :=
  .proven (combine_same_val_zero_sub_valid )

@[combine_valid, proof_pbv]
theorem combine_same_val_zero_xor_valid : Puddle.CTree.Pattern.Valid (same_val_zero_pattern .g_xor) := by
  proveCombineValid

@[legalization_status]
theorem combine_same_val_zero_xor_status :
    Status Unproven (same_val_zero_pattern .g_xor) :=
  .proven (combine_same_val_zero_xor_valid )

@[combine_valid, proof_pbv]
theorem combine_add_sub_reg_0_valid : Puddle.CTree.Pattern.Valid add_sub_reg_0_pattern := by
  proveCombineValid

@[legalization_status]
theorem combine_add_sub_reg_0_status :
    Status Unproven add_sub_reg_0_pattern :=
  .proven (combine_add_sub_reg_0_valid )

@[combine_valid, proof_pbv]
theorem combine_add_sub_reg_1_valid : Puddle.CTree.Pattern.Valid add_sub_reg_1_pattern := by
  proveCombineValid

@[legalization_status]
theorem combine_add_sub_reg_1_status :
    Status Unproven add_sub_reg_1_pattern :=
  .proven (combine_add_sub_reg_1_valid )

@[combine_valid, proof_pbv]
theorem combine_APlusBMinusCMinusB_valid : Puddle.CTree.Pattern.Valid APlusBMinusCMinusB_pattern := by
  proveCombineValid

@[legalization_status]
theorem combine_APlusBMinusCMinusB_status :
    Status Unproven APlusBMinusCMinusB_pattern :=
  .proven (combine_APlusBMinusCMinusB_valid )

@[combine_valid, proof_pbv]
theorem combine_AMinusBMinusCMinusC_valid : Puddle.CTree.Pattern.Valid AMinusBMinusCMinusC_pattern := by
  proveCombineValid

@[legalization_status]
theorem combine_AMinusBMinusCMinusC_status :
    Status Unproven AMinusBMinusCMinusC_pattern :=
  .proven (combine_AMinusBMinusCMinusC_valid )

@[combine_valid, proof_pbv]
theorem combine_AMinusBPlusCMinusA_valid : Puddle.CTree.Pattern.Valid AMinusBPlusCMinusA_pattern := by
  proveCombineValid

@[legalization_status]
theorem combine_AMinusBPlusCMinusA_status :
    Status Unproven AMinusBPlusCMinusA_pattern :=
  .proven (combine_AMinusBPlusCMinusA_valid )

@[combine_valid, proof_pbv]
theorem combine_AMinusBPlusBMinusC_valid : Puddle.CTree.Pattern.Valid AMinusBPlusBMinusC_pattern := by
  proveCombineValid

@[legalization_status]
theorem combine_AMinusBPlusBMinusC_status :
    Status Unproven AMinusBPlusBMinusC_pattern :=
  .proven (combine_AMinusBPlusBMinusC_valid )

@[combine_valid, proof_pbv]
theorem combine_AMinusBMinusA_valid : Puddle.CTree.Pattern.Valid AMinusBMinusA_pattern := by
  proveCombineValid

@[legalization_status]
theorem combine_AMinusBMinusA_status :
    Status Unproven AMinusBMinusA_pattern :=
  .proven (combine_AMinusBMinusA_valid )

@[combine_valid, proof_pbv]
theorem combine_APlusBMinusAPlusC_valid : Puddle.CTree.Pattern.Valid (APlusBMinusAPlusC_pattern true) := by
  proveCombineValid

@[legalization_status]
theorem combine_APlusBMinusAPlusC_status :
    Status Unproven (APlusBMinusAPlusC_pattern true) :=
  .proven (combine_APlusBMinusAPlusC_valid )

@[combine_valid, proof_pbv]
theorem combine_APlusBMinusCPlusA_valid : Puddle.CTree.Pattern.Valid (APlusBMinusAPlusC_pattern false) := by
  proveCombineValid

@[legalization_status]
theorem combine_APlusBMinusCPlusA_status :
    Status Unproven (APlusBMinusAPlusC_pattern false) :=
  .proven (combine_APlusBMinusCPlusA_valid )

@[combine_valid, proof_pbv]
theorem combine_select_same_val_valid : Puddle.CTree.Pattern.Valid select_same_val_pattern := by
  proveCombineValid

@[legalization_status]
theorem combine_select_same_val_status :
    Status Unproven select_same_val_pattern :=
  .proven (combine_select_same_val_valid )

@[combine_valid, proof_pbv]
theorem combine_select_ugt_umax_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_to_iminmax_pattern info .ugt .g_umax) := by
  proveCombineValid

@[legalization_status]
theorem combine_select_ugt_umax_status (info : LegalizerInfo) :
    Status Unproven (select_to_iminmax_pattern info .ugt .g_umax) :=
  .proven (combine_select_ugt_umax_valid info )

@[combine_valid, proof_pbv]
theorem combine_select_uge_umax_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_to_iminmax_pattern info .uge .g_umax) := by
  proveCombineValid

@[legalization_status]
theorem combine_select_uge_umax_status (info : LegalizerInfo) :
    Status Unproven (select_to_iminmax_pattern info .uge .g_umax) :=
  .proven (combine_select_uge_umax_valid info )

@[combine_valid, proof_pbv]
theorem combine_select_sgt_smax_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_to_iminmax_pattern info .sgt .g_smax) := by
  proveCombineValid

@[legalization_status]
theorem combine_select_sgt_smax_status (info : LegalizerInfo) :
    Status Unproven (select_to_iminmax_pattern info .sgt .g_smax) :=
  .proven (combine_select_sgt_smax_valid info )

@[combine_valid, proof_pbv]
theorem combine_select_sge_smax_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_to_iminmax_pattern info .sge .g_smax) := by
  proveCombineValid

@[legalization_status]
theorem combine_select_sge_smax_status (info : LegalizerInfo) :
    Status Unproven (select_to_iminmax_pattern info .sge .g_smax) :=
  .proven (combine_select_sge_smax_valid info )

@[combine_valid, proof_pbv]
theorem combine_select_ult_umin_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_to_iminmax_pattern info .ult .g_umin) := by
  proveCombineValid

@[legalization_status]
theorem combine_select_ult_umin_status (info : LegalizerInfo) :
    Status Unproven (select_to_iminmax_pattern info .ult .g_umin) :=
  .proven (combine_select_ult_umin_valid info )

@[combine_valid, proof_pbv]
theorem combine_select_ule_umin_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_to_iminmax_pattern info .ule .g_umin) := by
  proveCombineValid

@[legalization_status]
theorem combine_select_ule_umin_status (info : LegalizerInfo) :
    Status Unproven (select_to_iminmax_pattern info .ule .g_umin) :=
  .proven (combine_select_ule_umin_valid info )

@[combine_valid, proof_pbv]
theorem combine_select_slt_smin_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_to_iminmax_pattern info .slt .g_smin) := by
  proveCombineValid

@[legalization_status]
theorem combine_select_slt_smin_status (info : LegalizerInfo) :
    Status Unproven (select_to_iminmax_pattern info .slt .g_smin) :=
  .proven (combine_select_slt_smin_valid info )

@[combine_valid, proof_pbv]
theorem combine_select_sle_smin_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_to_iminmax_pattern info .sle .g_smin) := by
  proveCombineValid

@[legalization_status]
theorem combine_select_sle_smin_status (info : LegalizerInfo) :
    Status Unproven (select_to_iminmax_pattern info .sle .g_smin) :=
  .proven (combine_select_sle_smin_valid info )

@[combine_valid, proof_pbv]
theorem combine_zext_of_select_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_of_cast_pattern info .g_zext) := by
  proveCombineValid

@[legalization_status]
theorem combine_zext_of_select_status (info : LegalizerInfo) :
    Status Unproven (select_of_cast_pattern info .g_zext) :=
  .proven (combine_zext_of_select_valid info )

@[combine_valid, proof_pbv]
theorem combine_trunc_of_select_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_of_cast_pattern info .g_trunc) := by
  proveCombineValid

@[legalization_status]
theorem combine_trunc_of_select_status (info : LegalizerInfo) :
    Status Unproven (select_of_cast_pattern info .g_trunc) :=
  .proven (combine_trunc_of_select_valid info )

@[combine_valid, proof_pbv]
theorem combine_select_into_sub_valid : Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_sub false) := by
  proveCombineValid

@[legalization_status]
theorem combine_select_into_sub_status :
    Status Unproven (select_into_binop_pattern .g_sub false) :=
  .proven (combine_select_into_sub_valid )

@[combine_valid, proof_pbv]
theorem combine_select_into_sub_swapped_valid : Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_sub true) := by
  proveCombineValid

@[legalization_status]
theorem combine_select_into_sub_swapped_status :
    Status Unproven (select_into_binop_pattern .g_sub true) :=
  .proven (combine_select_into_sub_swapped_valid )

@[combine_valid, proof_pbv]
theorem combine_select_into_add_valid : Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_add false) := by
  proveCombineValid

@[legalization_status]
theorem combine_select_into_add_status :
    Status Unproven (select_into_binop_pattern .g_add false) :=
  .proven (combine_select_into_add_valid )

@[combine_valid, proof_pbv]
theorem combine_select_into_add_swapped_valid : Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_add true) := by
  proveCombineValid

@[legalization_status]
theorem combine_select_into_add_swapped_status :
    Status Unproven (select_into_binop_pattern .g_add true) :=
  .proven (combine_select_into_add_swapped_valid )

@[combine_valid, proof_pbv]
theorem combine_select_into_or_valid : Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_or false) := by
  proveCombineValid

@[legalization_status]
theorem combine_select_into_or_status :
    Status Unproven (select_into_binop_pattern .g_or false) :=
  .proven (combine_select_into_or_valid )

@[combine_valid, proof_pbv]
theorem combine_select_into_or_swapped_valid : Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_or true) := by
  proveCombineValid

@[legalization_status]
theorem combine_select_into_or_swapped_status :
    Status Unproven (select_into_binop_pattern .g_or true) :=
  .proven (combine_select_into_or_swapped_valid )

@[combine_valid, proof_pbv]
theorem combine_select_into_xor_valid : Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_xor false) := by
  proveCombineValid

@[legalization_status]
theorem combine_select_into_xor_status :
    Status Unproven (select_into_binop_pattern .g_xor false) :=
  .proven (combine_select_into_xor_valid )

@[combine_valid, proof_pbv]
theorem combine_select_into_xor_swapped_valid : Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_xor true) := by
  proveCombineValid

@[legalization_status]
theorem combine_select_into_xor_swapped_status :
    Status Unproven (select_into_binop_pattern .g_xor true) :=
  .proven (combine_select_into_xor_swapped_valid )

-- the `icmp` predicate is abstracted (with `maxHeartbeats 0`; at the default it times out first)
-- theorem combine_redundant_and_select_icmp_icmp_valid :
--     Puddle.CTree.Pattern.Valid (redundant_and_select_pattern .icmp .icmp) := by
--   proveCombineValid

-- the `icmp` predicate is abstracted
-- theorem combine_redundant_and_valid : Puddle.CTree.Pattern.Valid redundant_and_pattern := by
--   proveCombineValid

@[combine_valid, proof_pbv]
theorem combine_funnel_shift_fshr_or_lshr_valid :
    Puddle.CTree.Pattern.Valid (funnel_shift_or_shift_pattern .g_fshr .g_lshr false true) := by
  proveCombineValid

@[legalization_status]
theorem combine_funnel_shift_fshr_or_lshr_status :
    Status Unproven (funnel_shift_or_shift_pattern .g_fshr .g_lshr false true) :=
  .proven combine_funnel_shift_fshr_or_lshr_valid

@[combine_valid, proof_pbv]
theorem combine_funnel_shift_lshr_or_fshr_valid :
    Puddle.CTree.Pattern.Valid (funnel_shift_or_shift_pattern .g_fshr .g_lshr false false) := by
  proveCombineValid

@[legalization_status]
theorem combine_funnel_shift_lshr_or_fshr_status :
    Status Unproven (funnel_shift_or_shift_pattern .g_fshr .g_lshr false false) :=
  .proven combine_funnel_shift_lshr_or_fshr_valid

/-! ## Combines that match constants, decided by `pbv_decide`

Each combine is proven by `proveCombineValid` alone, as above. -/

@[combine_valid, proof_pbv]
theorem combine_right_identity_zero_sub_valid :
    Puddle.CTree.Pattern.Valid (right_identity_zero_pattern .g_sub) := by
  proveCombineValid

@[legalization_status]
theorem combine_right_identity_zero_sub_status :
    Status Unproven (right_identity_zero_pattern .g_sub) :=
  .proven (combine_right_identity_zero_sub_valid)

@[combine_valid, proof_pbv]
theorem combine_right_identity_zero_add_valid :
    Puddle.CTree.Pattern.Valid (right_identity_zero_pattern .g_add) := by
  proveCombineValid

@[legalization_status]
theorem combine_right_identity_zero_add_status :
    Status Unproven (right_identity_zero_pattern .g_add) :=
  .proven (combine_right_identity_zero_add_valid)

@[combine_valid, proof_pbv]
theorem combine_right_identity_zero_or_valid :
    Puddle.CTree.Pattern.Valid (right_identity_zero_pattern .g_or) := by
  proveCombineValid

@[legalization_status]
theorem combine_right_identity_zero_or_status :
    Status Unproven (right_identity_zero_pattern .g_or) :=
  .proven (combine_right_identity_zero_or_valid)

@[combine_valid, proof_pbv]
theorem combine_right_identity_zero_xor_valid :
    Puddle.CTree.Pattern.Valid (right_identity_zero_pattern .g_xor) := by
  proveCombineValid

@[legalization_status]
theorem combine_right_identity_zero_xor_status :
    Status Unproven (right_identity_zero_pattern .g_xor) :=
  .proven (combine_right_identity_zero_xor_valid)

@[combine_valid, proof_pbv]
theorem combine_right_identity_zero_shl_valid :
    Puddle.CTree.Pattern.Valid (right_identity_zero_pattern .g_shl) := by
  proveCombineValid

@[legalization_status]
theorem combine_right_identity_zero_shl_status :
    Status Unproven (right_identity_zero_pattern .g_shl) :=
  .proven (combine_right_identity_zero_shl_valid)

@[combine_valid, proof_pbv]
theorem combine_right_identity_zero_ashr_valid :
    Puddle.CTree.Pattern.Valid (right_identity_zero_pattern .g_ashr) := by
  proveCombineValid

@[legalization_status]
theorem combine_right_identity_zero_ashr_status :
    Status Unproven (right_identity_zero_pattern .g_ashr) :=
  .proven (combine_right_identity_zero_ashr_valid)

@[combine_valid, proof_pbv]
theorem combine_right_identity_zero_lshr_valid :
    Puddle.CTree.Pattern.Valid (right_identity_zero_pattern .g_lshr) := by
  proveCombineValid

@[legalization_status]
theorem combine_right_identity_zero_lshr_status :
    Status Unproven (right_identity_zero_pattern .g_lshr) :=
  .proven (combine_right_identity_zero_lshr_valid)

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_right_identity_one_int_valid :
--     Puddle.CTree.Pattern.Valid (right_identity_one_int_pattern) := by
--   proveCombineValid

@[combine_valid, proof_pbv]
theorem combine_binop_right_to_zero_valid :
    Puddle.CTree.Pattern.Valid (binop_right_to_zero_pattern) := by
  proveCombineValid

@[legalization_status]
theorem combine_binop_right_to_zero_status :
    Status Unproven (binop_right_to_zero_pattern) :=
  .proven (combine_binop_right_to_zero_valid)

@[combine_valid, proof_pbv]
theorem combine_binop_left_to_zero_shl_valid :
    Puddle.CTree.Pattern.Valid (binop_left_to_zero_pattern .g_shl) := by
  proveCombineValid

@[legalization_status]
theorem combine_binop_left_to_zero_shl_status :
    Status Unproven (binop_left_to_zero_pattern .g_shl) :=
  .proven (combine_binop_left_to_zero_shl_valid)

@[combine_valid, proof_pbv]
theorem combine_binop_left_to_zero_lshr_valid :
    Puddle.CTree.Pattern.Valid (binop_left_to_zero_pattern .g_lshr) := by
  proveCombineValid

@[legalization_status]
theorem combine_binop_left_to_zero_lshr_status :
    Status Unproven (binop_left_to_zero_pattern .g_lshr) :=
  .proven (combine_binop_left_to_zero_lshr_valid)

@[combine_valid, proof_pbv]
theorem combine_binop_left_to_zero_ashr_valid :
    Puddle.CTree.Pattern.Valid (binop_left_to_zero_pattern .g_ashr) := by
  proveCombineValid

@[legalization_status]
theorem combine_binop_left_to_zero_ashr_status :
    Status Unproven (binop_left_to_zero_pattern .g_ashr) :=
  .proven (combine_binop_left_to_zero_ashr_valid)

@[combine_valid, proof_pbv]
theorem combine_binop_left_to_zero_mul_valid :
    Puddle.CTree.Pattern.Valid (binop_left_to_zero_pattern .g_mul) := by
  proveCombineValid

@[legalization_status]
theorem combine_binop_left_to_zero_mul_status :
    Status Unproven (binop_left_to_zero_pattern .g_mul) :=
  .proven (combine_binop_left_to_zero_mul_valid)

@[combine_valid, proof_pbv]
theorem combine_sub_minus_one_valid :
    Puddle.CTree.Pattern.Valid (sub_minus_one_pattern) := by
  proveCombineValid

@[legalization_status]
theorem combine_sub_minus_one_status :
    Status Unproven (sub_minus_one_pattern) :=
  .proven (combine_sub_minus_one_valid)

@[combine_valid, proof_pbv]
theorem combine_ZeroMinusAPlusB_valid :
    Puddle.CTree.Pattern.Valid (ZeroMinusAPlusB_pattern) := by
  proveCombineValid

@[legalization_status]
theorem combine_ZeroMinusAPlusB_status :
    Status Unproven (ZeroMinusAPlusB_pattern) :=
  .proven (combine_ZeroMinusAPlusB_valid)

@[combine_valid, proof_pbv]
theorem combine_APlusZeroMinusB_valid :
    Puddle.CTree.Pattern.Valid (APlusZeroMinusB_pattern) := by
  proveCombineValid

@[legalization_status]
theorem combine_APlusZeroMinusB_status :
    Status Unproven (APlusZeroMinusB_pattern) :=
  .proven (combine_APlusZeroMinusB_valid)

@[combine_valid, proof_pbv]
theorem combine_AMinusZeroMinusB_valid :
    Puddle.CTree.Pattern.Valid (AMinusZeroMinusB_pattern) := by
  proveCombineValid

@[legalization_status]
theorem combine_AMinusZeroMinusB_status :
    Status Unproven (AMinusZeroMinusB_pattern) :=
  .proven (combine_AMinusZeroMinusB_valid)

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_sub_one_from_sub_valid :
--     Puddle.CTree.Pattern.Valid (sub_one_from_sub_pattern) := by
--   proveCombineValid

@[combine_valid, proof_pbv]
theorem combine_APlusC1MinusC2_valid :
    Puddle.CTree.Pattern.Valid (APlusC1MinusC2_pattern) := by
  proveCombineValid

@[legalization_status]
theorem combine_APlusC1MinusC2_status :
    Status Unproven (APlusC1MinusC2_pattern) :=
  .proven (combine_APlusC1MinusC2_valid)

@[combine_valid, proof_pbv]
theorem combine_C2MinusAPlusC1_valid :
    Puddle.CTree.Pattern.Valid (C2MinusAPlusC1_pattern) := by
  proveCombineValid

@[legalization_status]
theorem combine_C2MinusAPlusC1_status :
    Status Unproven (C2MinusAPlusC1_pattern) :=
  .proven (combine_C2MinusAPlusC1_valid)

@[combine_valid, proof_pbv]
theorem combine_AMinusC1MinusC2_valid :
    Puddle.CTree.Pattern.Valid (AMinusC1MinusC2_pattern) := by
  proveCombineValid

@[legalization_status]
theorem combine_AMinusC1MinusC2_status :
    Status Unproven (AMinusC1MinusC2_pattern) :=
  .proven (combine_AMinusC1MinusC2_valid)

@[combine_valid, proof_pbv]
theorem combine_C1MinusAMinusC2_valid :
    Puddle.CTree.Pattern.Valid (C1MinusAMinusC2_pattern) := by
  proveCombineValid

@[legalization_status]
theorem combine_C1MinusAMinusC2_status :
    Status Unproven (C1MinusAMinusC2_pattern) :=
  .proven (combine_C1MinusAMinusC2_valid)

@[combine_valid, proof_pbv]
theorem combine_AMinusC1PlusC2_valid :
    Puddle.CTree.Pattern.Valid (AMinusC1PlusC2_pattern) := by
  proveCombineValid

@[legalization_status]
theorem combine_AMinusC1PlusC2_status :
    Status Unproven (AMinusC1PlusC2_pattern) :=
  .proven (combine_AMinusC1PlusC2_valid)

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_sub_of_mul_const_valid :
--     Puddle.CTree.Pattern.Valid (sub_of_mul_const_pattern) := by
--   proveCombineValid

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_mul_by_neg_one_valid :
--     Puddle.CTree.Pattern.Valid (mul_by_neg_one_pattern) := by
--   proveCombineValid

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_mulo_by_2_valid :
--     Puddle.CTree.Pattern.Valid (mulo_by_2_pattern) := by
--   proveCombineValid

@[combine_valid, proof_pbv]
theorem combine_NotAPlusNegOne_valid :
    Puddle.CTree.Pattern.Valid (NotAPlusNegOne_pattern) := by
  proveCombineValid

@[legalization_status]
theorem combine_NotAPlusNegOne_status :
    Status Unproven (NotAPlusNegOne_pattern) :=
  .proven (combine_NotAPlusNegOne_valid)

@[combine_valid, proof_pbv]
theorem combine_add_shift_valid :
    Puddle.CTree.Pattern.Valid (add_shift_pattern false) := by
  proveCombineValid

@[legalization_status]
theorem combine_add_shift_status :
    Status Unproven (add_shift_pattern false) :=
  .proven (combine_add_shift_valid)

@[combine_valid, proof_pbv]
theorem combine_add_shift_swapped_valid :
    Puddle.CTree.Pattern.Valid (add_shift_pattern true) := by
  proveCombineValid

@[legalization_status]
theorem combine_add_shift_swapped_status :
    Status Unproven (add_shift_pattern true) :=
  .proven (combine_add_shift_swapped_valid)

@[combine_valid, proof_pbv]
theorem combine_or_and_xor_to_or_or_and_valid :
    Puddle.CTree.Pattern.Valid (or_and_xor_to_or_pattern .g_or .g_and) := by
  proveCombineValid

@[legalization_status]
theorem combine_or_and_xor_to_or_or_and_status :
    Status Unproven (or_and_xor_to_or_pattern .g_or .g_and) :=
  .proven (combine_or_and_xor_to_or_or_and_valid)

@[combine_valid, proof_pbv]
theorem combine_or_and_xor_to_or_and_or_valid :
    Puddle.CTree.Pattern.Valid (or_and_xor_to_or_pattern .g_and .g_or) := by
  proveCombineValid

@[legalization_status]
theorem combine_or_and_xor_to_or_and_or_status :
    Status Unproven (or_and_xor_to_or_pattern .g_and .g_or) :=
  .proven (combine_or_and_xor_to_or_and_or_valid)

@[combine_valid, proof_pbv]
theorem combine_or_and_xor_to_xor_or_or_and_valid :
    Puddle.CTree.Pattern.Valid (or_and_xor_to_xor_or_pattern .g_or .g_and) := by
  proveCombineValid

@[legalization_status]
theorem combine_or_and_xor_to_xor_or_or_and_status :
    Status Unproven (or_and_xor_to_xor_or_pattern .g_or .g_and) :=
  .proven (combine_or_and_xor_to_xor_or_or_and_valid)

@[combine_valid, proof_pbv]
theorem combine_or_and_xor_to_xor_or_and_or_valid :
    Puddle.CTree.Pattern.Valid (or_and_xor_to_xor_or_pattern .g_and .g_or) := by
  proveCombineValid

@[legalization_status]
theorem combine_or_and_xor_to_xor_or_and_or_status :
    Status Unproven (or_and_xor_to_xor_or_pattern .g_and .g_or) :=
  .proven (combine_or_and_xor_to_xor_or_and_or_valid)

@[combine_valid, proof_pbv]
theorem combine_simplify_neg_smax_valid :
    Puddle.CTree.Pattern.Valid (simplify_neg_minmax_pattern .g_smax .g_smin) := by
  proveCombineValid

@[legalization_status]
theorem combine_simplify_neg_smax_status :
    Status Unproven (simplify_neg_minmax_pattern .g_smax .g_smin) :=
  .proven (combine_simplify_neg_smax_valid)

@[combine_valid, proof_pbv]
theorem combine_simplify_neg_umax_valid :
    Puddle.CTree.Pattern.Valid (simplify_neg_minmax_pattern .g_umax .g_umin) := by
  proveCombineValid

@[legalization_status]
theorem combine_simplify_neg_umax_status :
    Status Unproven (simplify_neg_minmax_pattern .g_umax .g_umin) :=
  .proven (combine_simplify_neg_umax_valid)

@[combine_valid, proof_pbv]
theorem combine_simplify_neg_smin_valid :
    Puddle.CTree.Pattern.Valid (simplify_neg_minmax_pattern .g_smin .g_smax) := by
  proveCombineValid

@[legalization_status]
theorem combine_simplify_neg_smin_status :
    Status Unproven (simplify_neg_minmax_pattern .g_smin .g_smax) :=
  .proven (combine_simplify_neg_smin_valid)

@[combine_valid, proof_pbv]
theorem combine_simplify_neg_umin_valid :
    Puddle.CTree.Pattern.Valid (simplify_neg_minmax_pattern .g_umin .g_umax) := by
  proveCombineValid

@[legalization_status]
theorem combine_simplify_neg_umin_status :
    Status Unproven (simplify_neg_minmax_pattern .g_umin .g_umax) :=
  .proven (combine_simplify_neg_umin_valid)

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_eq_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .eq .ne) := by
--   proveCombineValid

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_ne_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .ne .eq) := by
--   proveCombineValid

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_ugt_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .ugt .ule) := by
--   proveCombineValid

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_uge_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .uge .ult) := by
--   proveCombineValid

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_ult_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .ult .uge) := by
--   proveCombineValid

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_ule_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .ule .ugt) := by
--   proveCombineValid

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_sgt_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .sgt .sle) := by
--   proveCombineValid

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_sge_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .sge .slt) := by
--   proveCombineValid

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_slt_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .slt .sge) := by
--   proveCombineValid

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_sle_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .sle .sgt) := by
--   proveCombineValid

@[combine_valid, proof_pbv]
theorem combine_double_icmp_zero_and_valid :
    Puddle.CTree.Pattern.Valid (double_icmp_zero_pattern .g_and .eq) := by
  proveCombineValid

@[legalization_status]
theorem combine_double_icmp_zero_and_status :
    Status Unproven (double_icmp_zero_pattern .g_and .eq) :=
  .proven (combine_double_icmp_zero_and_valid)

@[combine_valid, proof_pbv]
theorem combine_double_icmp_zero_or_valid :
    Puddle.CTree.Pattern.Valid (double_icmp_zero_pattern .g_or .ne) := by
  proveCombineValid

@[legalization_status]
theorem combine_double_icmp_zero_or_status :
    Status Unproven (double_icmp_zero_pattern .g_or .ne) :=
  .proven (combine_double_icmp_zero_or_valid)

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_udiv_by_pow2_valid :
--     Puddle.CTree.Pattern.Valid (udiv_by_pow2_pattern) := by
--   proveCombineValid

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_sdiv_exact_by_pow2_pos_valid :
--     Puddle.CTree.Pattern.Valid (sdiv_exact_by_pow2_pattern false) := by
--   proveCombineValid

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_sdiv_exact_by_pow2_neg_valid :
--     Puddle.CTree.Pattern.Valid (sdiv_exact_by_pow2_pattern true) := by
--   proveCombineValid

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_sdiv_by_pow2_pos_valid :
--     Puddle.CTree.Pattern.Valid (sdiv_by_pow2_pattern false) := by
--   proveCombineValid

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_sdiv_by_pow2_neg_valid :
--     Puddle.CTree.Pattern.Valid (sdiv_by_pow2_pattern true) := by
--   proveCombineValid

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_mul_to_shl_valid :
--     Puddle.CTree.Pattern.Valid (mul_to_shl_pattern) := by
--   proveCombineValid

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_urem_pow2_to_mask_valid :
--     Puddle.CTree.Pattern.Valid (urem_pow2_to_mask_pattern) := by
--   proveCombineValid

@[combine_valid, proof_pbv]
theorem combine_constant_fold_add_valid :
    Puddle.CTree.Pattern.Valid (constant_fold_binop_pattern .g_add (fun a b => a + b)) := by
  proveCombineValid

@[legalization_status]
theorem combine_constant_fold_add_status :
    Status Unproven (constant_fold_binop_pattern .g_add (fun a b => a + b)) :=
  .proven (combine_constant_fold_add_valid)

@[combine_valid, proof_pbv]
theorem combine_constant_fold_sub_valid :
    Puddle.CTree.Pattern.Valid (constant_fold_binop_pattern .g_sub ((· - ·))) := by
  proveCombineValid

@[legalization_status]
theorem combine_constant_fold_sub_status :
    Status Unproven (constant_fold_binop_pattern .g_sub ((· - ·))) :=
  .proven (combine_constant_fold_sub_valid)

@[combine_valid, proof_pbv]
theorem combine_constant_fold_smin_valid :
    Puddle.CTree.Pattern.Valid (constant_fold_binop_pattern .g_smin (min)) := by
  proveCombineValid

@[legalization_status]
theorem combine_constant_fold_smin_status :
    Status Unproven (constant_fold_binop_pattern .g_smin (min)) :=
  .proven (combine_constant_fold_smin_valid)

@[combine_valid, proof_pbv]
theorem combine_constant_fold_smax_valid :
    Puddle.CTree.Pattern.Valid (constant_fold_binop_pattern .g_smax (max)) := by
  proveCombineValid

@[legalization_status]
theorem combine_constant_fold_smax_status :
    Status Unproven (constant_fold_binop_pattern .g_smax (max)) :=
  .proven (combine_constant_fold_smax_valid)

@[combine_valid, proof_pbv]
theorem combine_select_constant_cmp_nonzero_valid :
    Puddle.CTree.Pattern.Valid (select_constant_cmp_pattern true) := by
  proveCombineValid

@[legalization_status]
theorem combine_select_constant_cmp_nonzero_status :
    Status Unproven (select_constant_cmp_pattern true) :=
  .proven (combine_select_constant_cmp_nonzero_valid)

@[combine_valid, proof_pbv]
theorem combine_select_constant_cmp_zero_valid :
    Puddle.CTree.Pattern.Valid (select_constant_cmp_pattern false) := by
  proveCombineValid

@[legalization_status]
theorem combine_select_constant_cmp_zero_status :
    Status Unproven (select_constant_cmp_pattern false) :=
  .proven (combine_select_constant_cmp_zero_valid)

@[combine_valid, proof_pbv]
theorem combine_sub_to_add_valid (info : LegalizerInfo) :
    Puddle.CTree.Pattern.Valid (sub_to_add_pattern info) := by
  proveCombineValid

@[legalization_status]
theorem combine_sub_to_add_status (info : LegalizerInfo) :
    Status Unproven (sub_to_add_pattern info) :=
  .proven (combine_sub_to_add_valid info)

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_redundant_and_select_icmp_constant_valid :
--     Puddle.CTree.Pattern.Valid (redundant_and_select_pattern .icmp .constant) := by
--   proveCombineValid

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_redundant_and_select_constant_icmp_valid :
--     Puddle.CTree.Pattern.Valid (redundant_and_select_pattern .constant .icmp) := by
--   proveCombineValid

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_redundant_and_select_constant_constant_valid :
--     Puddle.CTree.Pattern.Valid (redundant_and_select_pattern .constant .constant) := by
--   proveCombineValid

@[combine_valid, proof_pbv]
theorem combine_select_into_shl_valid :
    Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_shl false) := by
  proveCombineValid

@[legalization_status]
theorem combine_select_into_shl_status :
    Status Unproven (select_into_binop_pattern .g_shl false) :=
  .proven (combine_select_into_shl_valid)

@[combine_valid, proof_pbv]
theorem combine_select_into_shl_swapped_valid :
    Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_shl true) := by
  proveCombineValid

@[legalization_status]
theorem combine_select_into_shl_swapped_status :
    Status Unproven (select_into_binop_pattern .g_shl true) :=
  .proven (combine_select_into_shl_swapped_valid)

@[combine_valid, proof_pbv]
theorem combine_select_into_lshr_valid :
    Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_lshr false) := by
  proveCombineValid

@[legalization_status]
theorem combine_select_into_lshr_status :
    Status Unproven (select_into_binop_pattern .g_lshr false) :=
  .proven (combine_select_into_lshr_valid)

@[combine_valid, proof_pbv]
theorem combine_select_into_lshr_swapped_valid :
    Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_lshr true) := by
  proveCombineValid

@[legalization_status]
theorem combine_select_into_lshr_swapped_status :
    Status Unproven (select_into_binop_pattern .g_lshr true) :=
  .proven (combine_select_into_lshr_swapped_valid)

@[combine_valid, proof_pbv]
theorem combine_select_into_ashr_valid :
    Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_ashr false) := by
  proveCombineValid

@[legalization_status]
theorem combine_select_into_ashr_status :
    Status Unproven (select_into_binop_pattern .g_ashr false) :=
  .proven (combine_select_into_ashr_valid)

@[combine_valid, proof_pbv]
theorem combine_select_into_ashr_swapped_valid :
    Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_ashr true) := by
  proveCombineValid

@[legalization_status]
theorem combine_select_into_ashr_swapped_status :
    Status Unproven (select_into_binop_pattern .g_ashr true) :=
  .proven (combine_select_into_ashr_swapped_valid)

@[combine_valid, proof_pbv]
theorem combine_select_one_zero_valid :
    Puddle.CTree.Pattern.Valid (select_one_zero_pattern) := by
  proveCombineValid

@[legalization_status]
theorem combine_select_one_zero_status :
    Status Unproven (select_one_zero_pattern) :=
  .proven (combine_select_one_zero_valid)

@[combine_valid, proof_pbv]
theorem combine_select_allOnes_zero_valid :
    Puddle.CTree.Pattern.Valid (select_allOnes_zero_pattern) := by
  proveCombineValid

@[legalization_status]
theorem combine_select_allOnes_zero_status :
    Status Unproven (select_allOnes_zero_pattern) :=
  .proven (combine_select_allOnes_zero_valid)

@[combine_valid, proof_pbv]
theorem combine_select_zero_one_valid :
    Puddle.CTree.Pattern.Valid (select_zero_one_pattern) := by
  proveCombineValid

@[legalization_status]
theorem combine_select_zero_one_status :
    Status Unproven (select_zero_one_pattern) :=
  .proven (combine_select_zero_one_valid)

@[combine_valid, proof_pbv]
theorem combine_select_zero_allOnes_valid :
    Puddle.CTree.Pattern.Valid (select_zero_allOnes_pattern) := by
  proveCombineValid

@[legalization_status]
theorem combine_select_zero_allOnes_status :
    Status Unproven (select_zero_allOnes_pattern) :=
  .proven (combine_select_zero_allOnes_valid)

@[combine_valid, proof_pbv]
theorem combine_select_succ_valid :
    Puddle.CTree.Pattern.Valid (select_succ_pattern) := by
  proveCombineValid

@[legalization_status]
theorem combine_select_succ_status :
    Status Unproven (select_succ_pattern) :=
  .proven (combine_select_succ_valid)

@[combine_valid, proof_pbv]
theorem combine_select_pred_valid :
    Puddle.CTree.Pattern.Valid (select_pred_pattern) := by
  proveCombineValid

@[legalization_status]
theorem combine_select_pred_status :
    Status Unproven (select_pred_pattern) :=
  .proven (combine_select_pred_valid)

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_select_pow2_zero_valid :
--     Puddle.CTree.Pattern.Valid (select_pow2_zero_pattern) := by
--   proveCombineValid

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_select_zero_pow2_valid :
--     Puddle.CTree.Pattern.Valid (select_zero_pow2_pattern) := by
--   proveCombineValid

@[combine_valid, proof_pbv]
theorem combine_select_allOnes_const_valid :
    Puddle.CTree.Pattern.Valid (select_allOnes_const_pattern) := by
  proveCombineValid

@[legalization_status]
theorem combine_select_allOnes_const_status :
    Status Unproven (select_allOnes_const_pattern) :=
  .proven (combine_select_allOnes_const_valid)

@[combine_valid, proof_pbv]
theorem combine_select_const_allOnes_valid :
    Puddle.CTree.Pattern.Valid (select_const_allOnes_pattern) := by
  proveCombineValid

@[legalization_status]
theorem combine_select_const_allOnes_status :
    Status Unproven (select_const_allOnes_pattern) :=
  .proven (combine_select_const_allOnes_valid)

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_funnel_shift_right_zero_valid :
--     Puddle.CTree.Pattern.Valid (funnel_shift_zero_pattern .g_fshr true) := by
--   proveCombineValid

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_funnel_shift_left_zero_valid :
--     Puddle.CTree.Pattern.Valid (funnel_shift_zero_pattern .g_fshl false) := by
--   proveCombineValid

-- spurious counterexample: the overshift amount's hypotheses are abstracted
-- theorem combine_funnel_shift_overshift_l_valid :
--     Puddle.CTree.Pattern.Valid (funnel_shift_overshift_pattern .g_fshl) := by
--   proveCombineValid

-- spurious counterexample: the overshift amount's hypotheses are abstracted
-- theorem combine_funnel_shift_overshift_r_valid :
--     Puddle.CTree.Pattern.Valid (funnel_shift_overshift_pattern .g_fshr) := by
--   proveCombineValid

end Veir.GMIRCombines.CTreeProofs
