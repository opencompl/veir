module

public import Veir.Interfaces.FoldInterfaces.Soundness
public import Veir.Dialects.GMIR.OpInfo
import all Veir.Dialects.GMIR.OpInfo
import all Veir.FoldDecision
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.Refinement
import all Veir.IR.Attribute
import all Veir.Interpreter.Refinement.Basic
import all Veir.Interpreter.RuntimeValue.Conforms
import all Veir.Interpreter.RuntimeValue.Basic
meta import Lean.Elab.Tactic

/-!
# Soundness of the gMIR fold table

Every entry of `GMIR.tryFold` is proved against `GMIR.interpretOp'`. Widths are
symbolic here, so instead of bit-blasting, each entry reduces to the
width-generic facts below about overflow, comparisons against the extreme
values, and refinement of poison.
-/

namespace Veir
open Data

namespace GMIRFold

theorem uaddOverflow_zero_right (x : BitVec w) : x.uaddOverflow 0#w = false := by
  simp [BitVec.uaddOverflow]; omega
theorem uaddOverflow_zero_left (x : BitVec w) : (0#w).uaddOverflow x = false := by
  simp [BitVec.uaddOverflow]; omega
theorem uaddOverflow_allOnes_right (x : BitVec w) : x.uaddOverflow (BitVec.allOnes w) = (x != 0#w) := by
  rw [Bool.eq_iff_iff]; simp [BitVec.uaddOverflow, BitVec.toNat_eq]; omega
theorem uaddOverflow_allOnes_left (x : BitVec w) : (BitVec.allOnes w).uaddOverflow x = (x != 0#w) := by
  rw [Bool.eq_iff_iff]; simp [BitVec.uaddOverflow, BitVec.toNat_eq]; omega
theorem saddOverflow_zero_right (x : BitVec w) : x.saddOverflow 0#w = false := by
  have := BitVec.toInt_lt (x := x); have := BitVec.le_toInt x
  simp [BitVec.saddOverflow]; omega
theorem saddOverflow_zero_left (x : BitVec w) : (0#w).saddOverflow x = false := by
  have := BitVec.toInt_lt (x := x); have := BitVec.le_toInt x
  simp [BitVec.saddOverflow]; omega
theorem usubOverflow_zero_right (x : BitVec w) : x.usubOverflow 0#w = false := by
  simp [BitVec.usubOverflow]
theorem usubOverflow_zero_left (x : BitVec w) : (0#w).usubOverflow x = (x != 0#w) := by
  rw [Bool.eq_iff_iff]; simp [BitVec.usubOverflow, BitVec.toNat_eq]; omega
theorem ssubOverflow_zero_right (x : BitVec w) : x.ssubOverflow 0#w = false := by
  have := BitVec.toInt_lt (x := x); have := BitVec.le_toInt x
  simp [BitVec.ssubOverflow]; omega
theorem ule_zero (x : BitVec w) : x.ule 0#w = decide (x = 0#w) := by
  simp [BitVec.ule, BitVec.toNat_eq]
theorem zero_ule (x : BitVec w) : (0#w).ule x = true := by simp [BitVec.ule]
theorem ule_allOnes (x : BitVec w) : x.ule (BitVec.allOnes w) = true := by
  simp [BitVec.ule]; omega
theorem allOnes_ule (x : BitVec w) : (BitVec.allOnes w).ule x = decide (x = BitVec.allOnes w) := by
  simp [BitVec.ule, BitVec.toNat_eq]; omega
theorem ult_zero (x : BitVec w) : x.ult 0#w = false := by simp [BitVec.ult]
theorem allOnes_ult (x : BitVec w) : (BitVec.allOnes w).ult x = false := by simp [BitVec.ult]; omega
theorem sle_intMax (x : BitVec w) : x.sle (BitVec.intMax w) = true := by
  simp [BitVec.sle]; exact BitVec.toInt_le
theorem intMax_slt (x : BitVec w) : (BitVec.intMax w).slt x = false := by
  have := BitVec.toInt_le (x := x); simp [BitVec.slt]; omega
theorem intMax_sle (x : BitVec w) : (BitVec.intMax w).sle x = decide (x = BitVec.intMax w) := by
  have := BitVec.toInt_le (x := x)
  rw [Bool.eq_iff_iff]; simp [BitVec.sle, ← BitVec.toInt_inj]; omega
theorem intMin_sle' (x : BitVec w) : (BitVec.intMin w).sle x = true := BitVec.intMin_sle x
theorem slt_intMin (x : BitVec w) : x.slt (BitVec.intMin w) = false := by
  have := BitVec.toInt_intMin_le x; simp [BitVec.slt]; omega
theorem sle_intMin (x : BitVec w) : x.sle (BitVec.intMin w) = decide (x = BitVec.intMin w) := by
  have := BitVec.toInt_intMin_le x
  rw [Bool.eq_iff_iff]; simp [BitVec.sle, ← BitVec.toInt_inj]; omega
theorem allOnes_sshiftRight (n : Nat) : (BitVec.allOnes w).sshiftRight n = BitVec.allOnes w := by
  ext i hi; simp [BitVec.getElem_sshiftRight, BitVec.msb_allOnes (by omega : 0 < w)]
theorem srem_allOnes (x : BitVec w) : x.srem (BitVec.allOnes w) = 0#w := by
  cases w with
  | zero => exact Subsingleton.elim _ _
  | succ n => exact BitVec.srem_zero_of_dvd (by simp)

theorem val_isRefinedBy_val {a b : BitVec w} :
    (LLVM.Int.val a) ⊒ (LLVM.Int.val b) ↔ a = b := Iff.rfl
theorem val_isRefinedBy_poison {a : BitVec w} :
    ((LLVM.Int.val a) ⊒ LLVM.Int.poison) ↔ False := Iff.rfl
theorem ite_isRefinedBy {c : Prop} [Decidable c] {x y t : LLVM.Int w} :
    (if c then x else y) ⊒ t ↔ (c → x ⊒ t) ∧ (¬c → y ⊒ t) := by
  split <;> simp_all
theorem ite_id_isRefinedBy {c : Prop} [Decidable c] {x y : Id (LLVM.Int w)} {t : LLVM.Int w} :
    ((if c then x else y : Id (LLVM.Int w)) : LLVM.Int w) ⊒ t ↔ (c → x ⊒ t) ∧ (¬c → y ⊒ t) := by
  split <;> simp_all
theorem conforms_int {ty : TypeAttr} (h : ty.val = Attribute.of IntegerType t) :
    RuntimeValue.Conforms (.int bw v) ty ↔ t.bitwidth = bw := by
  obtain ⟨val, _⟩ := ty
  simp only at h
  subst h
  rfl
theorem setWidth_one (_h : 1 < w) : BitVec.setWidth w 1#1 = 1#w := by
  ext i hi; simp [BitVec.getElem_setWidth]
theorem ite_zero_allOnes (w : Nat) : (if 0 < w then 0#w else BitVec.allOnes w) = 0#w := by
  cases w <;> simp
theorem conforms_first {vs : Array RuntimeValue} (h : RuntimeValue.ArrayConforms vs tys)
    (hv : 0 < vs.size := by simp) : vs[0]!.Conforms tys[0]! :=
  h.2 0 hv
theorem shiftAmount_zero {w' : Nat} (w : Nat) :
    shiftAmount (w' := w') w (.val 0#w') = .val 0#w := by
  by_cases h : 0 < w <;> simp [shiftAmount, h]
  cases w <;> simp_all
theorem allOnes_not_lt_width (w : Nat) : ¬ (BitVec.allOnes w < BitVec.ofNat w w) := by
  have := Nat.lt_two_pow_self (n := w)
  simp [BitVec.lt_def, Nat.mod_eq_of_lt this]; omega
theorem carry_zero_right (x : BitVec w) : BitVec.carry w x 0#w false = false := by
  simp [BitVec.carry]; omega
theorem carry_zero_left (x : BitVec w) : BitVec.carry w 0#w x false = false := by
  simp [BitVec.carry]; omega
theorem getElem!_of_getElem? {α} [Inhabited α] {a : Array α} {i : Nat} {x : α}
    (h : a[i]? = some x) : a[i]! = x := by
  grind
theorem cast_poison {w₁ w₂ : Nat} (h : w₁ = w₂) : (LLVM.Int.poison : LLVM.Int w₁).cast h = .poison := rfl
theorem cast_val {w₁ w₂ : Nat} (v : BitVec w₁) (h : w₁ = w₂) :
    (LLVM.Int.val v).cast h = .val (v.cast h) := rfl
theorem of_integerType_inj {a b : IntegerType} :
    Attribute.of IntegerType a = Attribute.of IntegerType b ↔ a = b :=
  ⟨fun h => Attribute.integerType.inj h, fun h => h ▸ rfl⟩
theorem ite_lt_of_le {α : Type} {n w : Nat} (h : w ≤ n) (x y : α) :
    (if n < w then x else y) = y := by
  simp [Nat.not_lt.mpr h]
theorem int_isRefinedBy_int {s t : LLVM.Int w} :
    RuntimeValue.isRefinedBy (.int w s) (.int w t) ↔ s ⊒ t := by
  simp [RuntimeValue.isRefinedBy]
theorem id_pure (x : LLVM.Int w) : (pure x : Id (LLVM.Int w)) = x := rfl

end GMIRFold

open Lean Elab Tactic Meta in
/-- Split every variable of the given type into its constructors. -/
meta partial def casesOfType (type : Name) (arity : Nat) (g : MVarId) : MetaM (List MVarId) :=
  g.withContext do
    for d in ← getLCtx do
      unless d.isImplementationDetail do
        if (← instantiateMVars d.type).isAppOfArity type arity then
          let subgoals ← g.cases d.fvarId
          return (← subgoals.toList.mapM fun s => casesOfType type arity s.mvarId).flatten
    return [g]

open Lean Elab Tactic in
/-- Split every `LLVM.Int` variable into poison and a value. -/
elab "cases_ints" : tactic => liftMetaTactic (casesOfType ``Data.LLVM.Int 1)

open Lean Elab Tactic in
/-- Expose the width of every integer type as a variable. -/
elab "cases_integer_types" : tactic => liftMetaTactic (casesOfType ``IntegerType 0)

theorem GMIRFold.integerType_unique {x : Attribute} {a b : IntegerType}
    (h₁ : x = .integerType a) (h₂ : x = .integerType b) : a = b :=
  Attribute.integerType.inj (h₁.symm.trans h₂)

open Lean Elab Tactic Meta in
/-- Two hypotheses `x = .integerType a` and `x = .integerType b` about the same `x`
make `a` and `b` the same type; substitute one for the other. -/
meta def unifyIntTypes (g : MVarId) : MetaM (List MVarId) := g.withContext do
  let hyps := (← getLCtx).decls.toList.filterMap id |>.filter (!·.isImplementationDetail)
  for h₁ in hyps do
    for h₂ in hyps do
      if h₁.fvarId == h₂.fvarId then continue
      let some (_, x₁, r₁) := (← instantiateMVars h₁.type).eq? | continue
      let some (_, x₂, r₂) := (← instantiateMVars h₂.type).eq? | continue
      unless r₁.isAppOfArity ``Attribute.integerType 1 && r₂.isAppOfArity ``Attribute.integerType 1 do
        continue
      unless r₁.appArg!.isFVar && r₂.appArg!.isFVar && r₁.appArg! != r₂.appArg! do continue
      unless ← isDefEq x₁ x₂ do continue
      let eq ← mkAppM ``GMIRFold.integerType_unique #[mkFVar h₁.fvarId, mkFVar h₂.fvarId]
      let g ← g.assert `hInt (← inferType eq) eq
      let (h, g) ← g.intro1P
      let (_, g) ← substCore g h (symm := true) <|> substCore g h
      return [g]
  return [g]

open Lean Elab Tactic in
elab "unify_int_types" : tactic => liftMetaTactic unifyIntTypes

/-- Substitute the integer operands that the interpreter matched. -/
local macro "gmir_operands" : tactic => `(tactic| first
  | (have hs := ‹[_, _] = [_, _]›
     simp only [List.cons.injEq, and_true] at hs
     obtain ⟨h₁, h₂⟩ := hs
     subst h₁ h₂)
  | (have hs := ‹[_, _, _] = [_, _, _]›
     simp only [List.cons.injEq, and_true] at hs
     obtain ⟨h₁, h₂, h₃⟩ := hs
     subst h₁ h₂ h₃))

/-- The simp set that checks one alternative of a table entry. -/
local macro "gmir_simp" : tactic => `(tactic| simp_all [intZero, intOne, intAllOnes, intMin, intMax, knownInt, intIf,
    FoldDecision.resolveAll, FoldDecision.resolve,
    OperationResult.isRefinedBy, RuntimeValue.arrayIsRefinedBy, ↓GMIRFold.int_isRefinedBy_int, RuntimeValue.isRefinedBy,
    ControlFlowAction.optionIsRefinedBy, Id.run, GMIRFold.id_pure, GMIRFold.ite_id_isRefinedBy, GMIRFold.uaddOverflow_zero_right, GMIRFold.uaddOverflow_zero_left, GMIRFold.uaddOverflow_allOnes_right, GMIRFold.uaddOverflow_allOnes_left, GMIRFold.saddOverflow_zero_right, GMIRFold.saddOverflow_zero_left, GMIRFold.usubOverflow_zero_right, GMIRFold.usubOverflow_zero_left, GMIRFold.ssubOverflow_zero_right, GMIRFold.ule_zero, GMIRFold.zero_ule, GMIRFold.ule_allOnes, GMIRFold.allOnes_ule, GMIRFold.ult_zero, GMIRFold.allOnes_ult, GMIRFold.sle_intMax, GMIRFold.intMax_slt, GMIRFold.intMax_sle, GMIRFold.intMin_sle', GMIRFold.slt_intMin, GMIRFold.sle_intMin, GMIRFold.allOnes_sshiftRight, GMIRFold.srem_allOnes, GMIRFold.val_isRefinedBy_val, GMIRFold.val_isRefinedBy_poison, GMIRFold.ite_isRefinedBy, BitVec.zero_shiftLeft, BitVec.zero_ushiftRight, BitVec.zero_udiv, BitVec.udiv_one, BitVec.zero_umod, BitVec.umod_one, BitVec.zero_sdiv, BitVec.sdiv_one,
    LLVM.Int.add, LLVM.Int.sub, LLVM.Int.mul, LLVM.Int.and, LLVM.Int.or, LLVM.Int.xor,
    LLVM.Int.sdiv, LLVM.Int.udiv, LLVM.Int.srem, LLVM.Int.urem, LLVM.Int.shl, LLVM.Int.lshr,
    LLVM.Int.ashr, LLVM.Int.sshlSat, LLVM.Int.ushlSat, LLVM.Int.saddSat, LLVM.Int.uaddSat,
    LLVM.Int.ssubSat, LLVM.Int.usubSat, LLVM.Int.smin, LLVM.Int.smax, LLVM.Int.umin,
    LLVM.Int.umax, LLVM.Int.icmp, LLVM.Int.zext, LLVM.Int.uaddOverflowFlag,
    LLVM.Int.usubOverflowFlag, LLVM.Int.isSignedDivisionUB, LLVM.Int.isUnsignedDivisionUB,
    GMIRFold.of_integerType_inj, GMIRFold.ite_lt_of_le, GMIRFold.setWidth_one, GMIRFold.cast_poison, GMIRFold.cast_val, LLVM.IntPred.eval, ↓GMIRFold.shiftAmount_zero, shiftAmount, GMIRFold.ite_zero_allOnes, GMIRFold.carry_zero_right, GMIRFold.carry_zero_left, GMIRFold.allOnes_not_lt_width, Nat.forall_lt_succ_left', zextOrTrunc, uaddWithCarry, usubWithBorrow])

/--
Prove one table entry, once the operands are substituted: take its chain of
alternatives apart, then check each alternative against the interpreter.
-/
local macro "gmir_fold_entry" : tactic => `(tactic| (
  repeat' ((try dsimp only) <;> first
    | apply FoldTable.orElse_sound
    | apply FoldTable.useOperandIf_sound
    | apply FoldTable.useConstantIf_sound
    | apply FoldTable.ite_sound
    | apply FoldTable.some_sound
    | apply FoldTable.none_sound
    | (apply FoldTable.bind_sound
       intro o ho
       unfold icmpOutcome? at ho
       split at ho <;> (try split at ho) <;> simp at ho <;> subst ho)
    | (intro _hc; apply FoldTable.some_sound)
    | (intro _hc; apply FoldTable.ite_sound))
  all_goals intros
  all_goals gmir_simp
  all_goals (obtain h | h := ‹_ ∨ _› <;> gmir_simp)))

set_option hygiene false in
/--
Interpret the operation on the substituted operands, drop the branches that fail
or trigger UB, and relate the table's view of the result types to the
interpreter's, then prove the entry.
-/
local macro "gmir_arm" : tactic => `(tactic| (
    simp only [GMIR.interpretOp'] at hInterp
    repeat' (split at hInterp)
    all_goals (try (simp at hInterp; done))
    all_goals gmir_operands
    all_goals (try obtain rfl := Decidable.of_not_not ‹¬_ ≠ _›)
    all_goals (simp only [LLVM.Int.cast_self, Interp.pure_eq, Interp.ok.injEq] at hInterp)
    all_goals subst hInterp
    all_goals rcases hl with rfl | rfl
    all_goals rcases hr with rfl | rfl
    all_goals (try rcases hc with rfl | rfl)
    all_goals cases_ints
    all_goals clear hAgree
    all_goals replace hConform := GMIRFold.conforms_first hConform
    all_goals simp only [List.getElem!_toArray, List.getElem!_cons_zero] at hConform
    all_goals (try split at hFold)
    all_goals (try obtain rfl := GMIRFold.getElem!_of_getElem? ‹resultTypes[0]? = _›)
    all_goals (try obtain rfl := GMIRFold.getElem!_of_getElem? ‹resultTypes[1]? = _›)
    all_goals unify_int_types
    all_goals (try clear ‹resultTypes[0]? = some resultTypes[0]!›)
    all_goals (try clear ‹resultTypes[1]? = some resultTypes[1]!›)
    all_goals (try rw [GMIRFold.conforms_int ‹resultTypes[0]!.val = _›] at hConform)
    all_goals cases_integer_types
    all_goals (try subst hConform)
    all_goals revert decisions
    all_goals gmir_fold_entry))

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
/--
The gMIR fold table is sound: whenever it decides that an operation folds, the
decisions resolve, against any operands that agree with the known ones, to
values that refine the results of interpreting the operation. The results must
have the declared result types, as the verifier guarantees.
-/
public theorem GMIR.tryFold_sound
    (hFold : GMIR.tryFold op properties resultTypes known = some decisions)
    (hAgree : FoldTable.Agrees known operands)
    (hInterp : GMIR.interpretOp' op properties resultTypes operands blockOperands mem =
      .ok results)
    (hConform : RuntimeValue.ArrayConforms results.1 resultTypes) :
    ∃ replacements, FoldDecision.resolveAll decisions operands = some replacements ∧
      OperationResult.isRefinedBy results (replacements, mem, none) := by
  unfold GMIR.tryFold at hFold
  split at hFold
  all_goals first
    | (simp at hFold; done)
    | (obtain ⟨a, b, c, rfl, hl, hr, hc⟩ := hAgree.triple ‹_›
       gmir_arm)
    | (obtain ⟨a, b, rfl, hl, hr⟩ := hAgree.pair ‹_›
       gmir_arm)

end Veir
