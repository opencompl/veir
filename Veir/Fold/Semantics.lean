import Veir.Fold
import Veir.Interpreter.Refinement.Lemmas

/-!
  # Semantics of constant folding

  This file states and proves refinement properties of the executable folding
  infrastructure in `Veir.Fold`.  The proofs are layered so that the pure fold
  tables can be checked independently of IR mutation by `PatternRewriter`.

  The proof is organized into these layers:
  * soundness of every partial-fold table entry;
  * agreement between `ValuePtr.constantValue` and interpreted SSA values
    (`Veir.Fold.Agree`);
  * correctness of constant materialization (`Veir.Fold.Materialize`); and
  * lifting the decision-level theorem through the local folding rewrite
    (`Veir.Fold.Rewrite`).
-/

namespace Veir

@[simp] private theorem Interp.bind_none {α β : Type} (f : α → Interp β) :
    ((none : Interp α) >>= f : Interp β) = none := rfl

@[simp] private theorem Interp.bind_ok {α β : Type} (value : α) (f : α → Interp β) :
    ((some (.ok value) : Interp α) >>= f : Interp β) = f value := rfl

@[simp] private theorem Interp.bind_ub {α β : Type} (f : α → Interp β) :
    ((some (UBOr.ub) : Interp α) >>= f : Interp β) = some UBOr.ub := rfl

@[simp] private theorem Interp.pure_bind {α β : Type} (value : α) (f : α → Interp β) :
    ((pure value : Interp α) >>= f : Interp β) = f value := rfl

@[simp] private theorem Interp.pure_eq {α : Type} (value : α) :
    (pure value : Interp α) = some (.ok value) := rfl

/-- A syntactically known operand agrees with its runtime value. -/
def KnownOperand.Agrees (known : Option RuntimeValue) (actual : RuntimeValue) : Prop :=
  match known with
  | none => True
  | some value => value = actual

/--
  The runtime operands agree pointwise with the constants discovered in the
  IR. Unknown operands impose no constraint.
-/
def ConstOperands.Agree (known : Array (Option RuntimeValue))
    (actual : Array RuntimeValue) : Prop :=
  known.size = actual.size ∧
    ∀ (i : Nat) value, known[i]? = some (some value) → actual[i]? = some value

theorem ConstOperands.Agree.singleton {known : Option RuntimeValue}
    {actual : Array RuntimeValue} (h : ConstOperands.Agree #[known] actual) :
    actual = #[actual[0]!] ∧ KnownOperand.Agrees known actual[0]! := by
  have hSize : actual.size = 1 := by
    simpa [ConstOperands.Agree] using h.1.symm
  constructor
  · apply Array.ext
    · simp [hSize]
    · intro i hi _
      have : i = 0 := by omega
      subst i
      rw [getElem!_pos actual 0 (by omega)]
      simp
  · cases known with
    | none => trivial
    | some value =>
      simp only [KnownOperand.Agrees]
      have hValue := h.2 0 value (by simp)
      rw [Array.getElem?_eq_getElem (by omega)] at hValue
      rw [getElem!_pos actual 0 (by omega)]
      exact Option.some.inj hValue |>.symm

theorem ConstOperands.Agree.pair {known₀ known₁ : Option RuntimeValue}
    {actual : Array RuntimeValue} (h : ConstOperands.Agree #[known₀, known₁] actual) :
    actual = #[actual[0]!, actual[1]!] ∧
      KnownOperand.Agrees known₀ actual[0]! ∧ KnownOperand.Agrees known₁ actual[1]! := by
  have hSize : actual.size = 2 := by
    simpa [ConstOperands.Agree] using h.1.symm
  constructor
  · apply Array.ext
    · simp [hSize]
    · intro i hi _
      have : i = 0 ∨ i = 1 := by omega
      rcases this with rfl | rfl
      · rw [getElem!_pos actual 0 (by omega)]
        simp
      · rw [getElem!_pos actual 1 (by omega)]
        simp
  · constructor
    · cases known₀ with
      | none => trivial
      | some value =>
        simp only [KnownOperand.Agrees]
        have hValue := h.2 0 value (by simp)
        rw [Array.getElem?_eq_getElem (by omega)] at hValue
        rw [getElem!_pos actual 0 (by omega)]
        exact Option.some.inj hValue |>.symm
    · cases known₁ with
      | none => trivial
      | some value =>
        simp only [KnownOperand.Agrees]
        have hValue := h.2 1 value (by simp)
        rw [Array.getElem?_eq_getElem (by omega)] at hValue
        rw [getElem!_pos actual 1 (by omega)]
        exact Option.some.inj hValue |>.symm

/-- Forget knowledge about the only operand. -/
theorem ConstOperands.Agree.forgetSingleton {known : Option RuntimeValue}
    {actual : Array RuntimeValue} (h : ConstOperands.Agree #[known] actual) :
    ConstOperands.Agree #[none] actual := by
  grind [ConstOperands.Agree]

/-- Forget knowledge about the first of two operands. -/
theorem ConstOperands.Agree.forgetPairFirst {known₀ known₁ : Option RuntimeValue}
    {actual : Array RuntimeValue} (h : ConstOperands.Agree #[known₀, known₁] actual) :
    ConstOperands.Agree #[none, known₁] actual := by
  grind [ConstOperands.Agree]

theorem ConstOperands.Agree.forgetSingleton_of_toList
    {known : Array (Option RuntimeValue)} {known₀ : Option RuntimeValue}
    {actual : Array RuntimeValue} (h : ConstOperands.Agree known actual)
    (hList : known.toList = [known₀]) : ConstOperands.Agree #[none] actual := by
  have hKnown : known = #[known₀] := Array.toList_inj.mp (by simpa using hList)
  subst known
  exact h.forgetSingleton

theorem ConstOperands.Agree.forgetPairFirst_of_toList
    {known : Array (Option RuntimeValue)} {known₀ known₁ : Option RuntimeValue}
    {actual : Array RuntimeValue} (h : ConstOperands.Agree known actual)
    (hList : known.toList = [known₀, known₁]) :
    ConstOperands.Agree #[none, known₁] actual := by
  have hKnown : known = #[known₀, known₁] := Array.toList_inj.mp (by simpa using hList)
  subst known
  exact h.forgetPairFirst

theorem ConstOperands.Agree.rhsReg_of_toList
    {known : Array (Option RuntimeValue)} {known₀ : Option RuntimeValue}
    {c : Data.RISCV.Reg} {value : BitVec 64} {actual : Array RuntimeValue}
    (h : ConstOperands.Agree known actual)
    (hList : known.toList = [known₀, some (.reg c)]) (hValue : c.val = value) :
    ConstOperands.Agree #[none, some (.reg (Data.RISCV.li value))] actual := by
  have h' := h.forgetPairFirst_of_toList hList
  have hc : c = Data.RISCV.li value := by cases c; simp_all [Data.RISCV.li]
  simpa [hc] using h'

theorem ConstOperands.Agree.rhsInt_of_toList
    {known : Array (Option RuntimeValue)} {known₀ : Option RuntimeValue}
    {bw : Nat} {rhs expected : Data.LLVM.Int bw} {actual : Array RuntimeValue}
    (hAgree : ConstOperands.Agree known actual)
    (hList : known.toList = [known₀, some (.int bw rhs)]) (hRhs : rhs = expected) :
    ConstOperands.Agree #[none, some (.int bw expected)] actual := by
  subst rhs
  exact hAgree.forgetPairFirst_of_toList hList

theorem ConstOperands.Agree.actual_eq_knownValues
    {known : Array (Option RuntimeValue)} {actual : Array RuntimeValue}
    (hAgree : ConstOperands.Agree known actual)
    (hAll : known.all (·.isSome)) : actual = known.map (·.get!) := by
  apply Array.ext
  · simp [hAgree.1]
  · intro i hiActual hiKnown
    have hi : i < known.size := by simpa [hAgree.1] using hiActual
    have hSome : known[i].isSome := (Array.all_eq_true.mp hAll) i hi
    obtain ⟨value, hValue⟩ := Option.isSome_iff_exists.mp hSome
    have hKnownAt : known[i]? = some (some value) := by
      rw [Array.getElem?_eq_getElem hi, hValue]
    have hActualAt := hAgree.2 i value hKnownAt
    rw [Array.getElem?_eq_getElem hiActual] at hActualAt
    simpa [hValue] using Option.some.inj hActualAt

theorem Array.eq_singleton_getElem! [Inhabited α] {values : Array α}
    (hSize : values.size = 1) :
    values = #[values[0]!] := by
  apply Array.ext
  · simp [hSize]
  · intro i hi _
    have : i = 0 := by omega
    subst i
    rw [getElem!_pos values 0 (by omega)]
    simp

/-- The runtime behavior represented directly by a fold-table outcome. -/
def FoldOutcome.target (outcome : FoldOutcome) (actualOperands : Array RuntimeValue)
    (source : Interp (Array RuntimeValue)) : Interp (Array RuntimeValue) :=
  match outcome with
  | .operand j => pure #[actualOperands[j]!]
  | .constant value => pure #[value]
  | .evaluate => source

/--
  A fold outcome is sound when replacing the source operation by the outcome's
  direct runtime behavior refines the source operation.

  The `.evaluate` outcome denotes the source behavior here. A later theorem
  connects the compile-time call to `foldEvaluate` with that same behavior.
-/
def FoldOutcome.Refines (outcome : FoldOutcome) (opCode : OpCode)
    (properties : HasOpInfo.propertiesOf opCode) (resultTypes : Array TypeAttr)
    (actualOperands : Array RuntimeValue) : Prop :=
  let source := foldEvaluate opCode properties resultTypes actualOperands
  Interp.isRefinedBy RuntimeValue.arrayIsRefinedBy source
    (outcome.target actualOperands source)

/-- Generic evaluation outcomes are sound by reflexivity. -/
theorem FoldOutcome.evaluate_refines (opCode : OpCode)
    (properties : HasOpInfo.propertiesOf opCode) (resultTypes : Array TypeAttr)
    (actualOperands : Array RuntimeValue) :
    FoldOutcome.Refines .evaluate opCode properties resultTypes actualOperands := by
  simp only [FoldOutcome.Refines, FoldOutcome.target]
  cases h : foldEvaluate opCode properties resultTypes actualOperands with
  | none => simp [Interp.isRefinedBy]
  | some result =>
    cases result <;> simp [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_refl]

/-- The runtime behavior represented by a resolved fold decision. -/
def FoldDecision.target (decision : FoldDecision) (actualOperands : Array RuntimeValue)
    (source : Interp (Array RuntimeValue)) : Interp (Array RuntimeValue) :=
  match decision with
  | .useOperand j => pure #[actualOperands[j]!]
  | .useConstant value => pure #[value]
  | .noFold => source

/-- A resolved fold decision refines the source operation. -/
def FoldDecision.Refines (decision : FoldDecision) (opCode : OpCode)
    (properties : HasOpInfo.propertiesOf opCode) (resultTypes : Array TypeAttr)
    (actualOperands : Array RuntimeValue) : Prop :=
  let source := foldEvaluate opCode properties resultTypes actualOperands
  Interp.isRefinedBy RuntimeValue.arrayIsRefinedBy source
    (decision.target actualOperands source)

/-- Declining to fold is always sound. -/
theorem FoldDecision.noFold_refines (opCode : OpCode)
    (properties : HasOpInfo.propertiesOf opCode) (resultTypes : Array TypeAttr)
    (actualOperands : Array RuntimeValue) :
    FoldDecision.Refines .noFold opCode properties resultTypes actualOperands := by
  simp only [FoldDecision.Refines, FoldDecision.target]
  cases h : foldEvaluate opCode properties resultTypes actualOperands with
  | none => simp [Interp.isRefinedBy]
  | some result =>
    cases result <;> simp [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_refl]

theorem OpCode.foldsTo_evaluate_allSome (opCode : OpCode)
    (properties : HasOpInfo.propertiesOf opCode)
    (resultTypes : Array TypeAttr)
    (knownOperands : Array (Option RuntimeValue))
    (hFold : OpCode.foldsTo opCode properties resultTypes knownOperands = some .evaluate) :
    knownOperands.all (·.isSome) := by
  unfold OpCode.foldsTo at hFold
  split at hFold
  · simp_all
  · cases opCode with
    | arith op =>
      cases op <;> simp [Arith.foldsTo] at hFold
      all_goals split at hFold <;> simp_all
      all_goals try (split at hFold <;> simp_all)
    | llvm op =>
      cases op <;> simp [Llvm.foldsTo] at hFold
      all_goals split at hFold <;> simp_all
      all_goals try (split at hFold <;> simp_all)
    | riscv op =>
      cases op <;> simp [Riscv.foldsTo] at hFold
      all_goals split at hFold <;> simp_all
      all_goals try (split at hFold <;> simp_all)
    | mod_arith op =>
      cases op <;> simp [Mod_Arith.foldsTo, Option.bind] at hFold
      all_goals split at hFold <;> simp_all
      all_goals try (split at hFold <;> simp_all)
    | _ => contradiction

theorem FoldDecision.partial_refines (opCode : OpCode)
    (properties : HasOpInfo.propertiesOf opCode)
    (knownOperands : Array (Option RuntimeValue)) (outcome : FoldOutcome)
    (resultTypes : Array TypeAttr) (actualOperands : Array RuntimeValue)
    (hFold : OpCode.foldsTo opCode properties resultTypes knownOperands = some outcome)
    (hNotEvaluate : outcome ≠ .evaluate)
    (hSound : FoldOutcome.Refines outcome opCode properties resultTypes actualOperands) :
    FoldDecision.Refines (foldDecision opCode properties resultTypes knownOperands)
      opCode properties resultTypes actualOperands := by
  unfold foldDecision
  split
  · exact FoldDecision.noFold_refines opCode properties resultTypes actualOperands
  · split
    · exact FoldDecision.noFold_refines opCode properties resultTypes actualOperands
    · rw [hFold]
      cases outcome with
      | operand j =>
        simpa [FoldDecision.Refines, FoldDecision.target,
          FoldOutcome.Refines, FoldOutcome.target] using hSound
      | constant value =>
        simpa [FoldDecision.Refines, FoldDecision.target,
          FoldOutcome.Refines, FoldOutcome.target] using hSound
      | evaluate => contradiction

theorem FoldDecision.evaluate_refines (opCode : OpCode)
    (properties : HasOpInfo.propertiesOf opCode)
    (knownOperands : Array (Option RuntimeValue))
    (resultTypes : Array TypeAttr) (actualOperands : Array RuntimeValue)
    (hFold : OpCode.foldsTo opCode properties resultTypes knownOperands = some .evaluate)
    (hAgree : ConstOperands.Agree knownOperands actualOperands) :
    FoldDecision.Refines (foldDecision opCode properties resultTypes knownOperands)
      opCode properties resultTypes actualOperands := by
  have hAll := OpCode.foldsTo_evaluate_allSome opCode properties resultTypes knownOperands hFold
  have hActual := hAgree.actual_eq_knownValues hAll
  unfold foldDecision
  split
  · exact FoldDecision.noFold_refines opCode properties resultTypes actualOperands
  · split
    · exact FoldDecision.noFold_refines opCode properties resultTypes actualOperands
    · rw [hFold]
      simp only
      rw [hActual]
      cases hEval : foldEvaluate opCode properties resultTypes
          (knownOperands.map fun x => x.get!) with
      | none =>
        exact FoldDecision.noFold_refines opCode properties resultTypes
          (knownOperands.map fun x => x.get!)
      | some result =>
        cases result with
        | ub =>
          simp [hEval, FoldDecision.Refines, FoldDecision.target, Interp.isRefinedBy]
        | ok results =>
          by_cases hSize : results.size = 1
          · simp [hEval, hSize, FoldDecision.Refines, FoldDecision.target,
              Interp.isRefinedBy]
            constructor
            · simp [hSize]
            · intro i hi
              have : i = 0 := by omega
              subst i
              rw [getElem!_pos results 0 hi]
              exact RuntimeValue.isRefinedBy_refl _
          · simp [hSize, FoldDecision.noFold_refines]

theorem FoldDecision.refines_of_foldsTo_refines (opCode : OpCode)
    (properties : HasOpInfo.propertiesOf opCode)
    (knownOperands : Array (Option RuntimeValue))
    (resultTypes : Array TypeAttr) (actualOperands : Array RuntimeValue)
    (hAgree : ConstOperands.Agree knownOperands actualOperands)
    (hSound : ∀ outcome,
      OpCode.foldsTo opCode properties resultTypes knownOperands = some outcome →
      FoldOutcome.Refines outcome opCode properties resultTypes actualOperands) :
    FoldDecision.Refines (foldDecision opCode properties resultTypes knownOperands)
      opCode properties resultTypes actualOperands := by
  cases hFold : OpCode.foldsTo opCode properties resultTypes knownOperands with
  | none =>
    unfold foldDecision
    split
    · exact FoldDecision.noFold_refines opCode properties resultTypes actualOperands
    · split
      · exact FoldDecision.noFold_refines opCode properties resultTypes actualOperands
      · rw [hFold]
        exact FoldDecision.noFold_refines opCode properties resultTypes actualOperands
  | some outcome =>
    cases outcome with
    | operand j =>
      exact FoldDecision.partial_refines opCode properties knownOperands (.operand j)
        resultTypes actualOperands hFold (by simp) (hSound _ hFold)
    | constant value =>
      exact FoldDecision.partial_refines opCode properties knownOperands (.constant value)
        resultTypes actualOperands hFold (by simp) (hSound _ hFold)
    | evaluate =>
      exact FoldDecision.evaluate_refines opCode properties knownOperands resultTypes
        actualOperands hFold hAgree

theorem ConstOperands.Agree.binaryIntShape {bw : Nat} {rhs : Data.LLVM.Int bw}
    {actualOperands : Array RuntimeValue}
    (hAgree : ConstOperands.Agree #[none, some (.int bw rhs)] actualOperands) :
    ∃ lhs, actualOperands = #[lhs, .int bw rhs] := by
  let lhs := actualOperands[0]!
  have hShape : actualOperands = #[lhs, actualOperands[1]!] := hAgree.pair.1
  have hRhs : RuntimeValue.int bw rhs = actualOperands[1]! := hAgree.pair.2.2
  exact ⟨lhs, hShape.trans (by rw [← hRhs])⟩

@[simp] private theorem BitVec.saddOverflow_zero_right {w : Nat} (x : BitVec w) :
    x.saddOverflow 0 = false := by
  have hUpper := @BitVec.toInt_lt w x
  have hLower := @BitVec.le_toInt w x
  simp [BitVec.saddOverflow]
  omega

@[simp] private theorem BitVec.uaddOverflow_zero_right {w : Nat} (x : BitVec w) :
    x.uaddOverflow 0 = false := by
  have hUpper := x.toNat_lt_twoPow_of_le (Nat.le_refl w)
  simp [BitVec.uaddOverflow]
  omega

@[simp] private theorem Data.LLVM.Int.add_zero_flags {w : Nat}
    (x : Data.LLVM.Int w) (nsw nuw : Bool) :
    Data.LLVM.Int.add x (.val 0) nsw nuw = x := by
  cases x with
  | poison => rfl
  | val value =>
    have hSigned := BitVec.saddOverflow_zero_right value
    have hUnsigned := BitVec.uaddOverflow_zero_right value
    simp only [Data.LLVM.Int.add]
    split <;> simp_all <;> rfl

@[simp] private theorem Data.LLVM.Int.add_cast_zero_flags {w₁ w₂ : Nat}
    (x : Data.LLVM.Int w₂) (h : w₁ = w₂) (nsw nuw : Bool) :
    Data.LLVM.Int.add x (.val ((0#w₁).cast h)) nsw nuw = x := by
  subst w₂
  simpa using Data.LLVM.Int.add_zero_flags x nsw nuw

private theorem Data.LLVM.Int.add_zero_refines {w : Nat}
    (x : Data.LLVM.Int w) (nsw nuw : Bool) :
    Data.LLVM.Int.add x (.val 0) nsw nuw ⊒ x := by
  rw [Data.LLVM.Int.add_zero_flags]
  exact isRefinedBy_refl _

private theorem Data.LLVM.Int.sub_zero_refines {w : Nat}
    (x : Data.LLVM.Int w) (nsw nuw : Bool) :
    Data.LLVM.Int.sub x (.val 0) nsw nuw ⊒ x := by
  grind

private theorem Data.LLVM.Int.mul_zero_refines {w : Nat}
    (x : Data.LLVM.Int w) (nsw nuw : Bool) :
    Data.LLVM.Int.mul x (.val 0) nsw nuw ⊒ .val 0 := by
  grind

private theorem Data.LLVM.Int.mul_one_refines {w : Nat}
    (x : Data.LLVM.Int w) (nsw nuw : Bool) :
    Data.LLVM.Int.mul x (.val 1) nsw nuw ⊒ x := by
  grind

private theorem Data.LLVM.Int.and_zero_refines {w : Nat}
    (x : Data.LLVM.Int w) : Data.LLVM.Int.and x (.val 0) ⊒ .val 0 := by
  grind

private theorem Data.LLVM.Int.and_allOnes_refines {w : Nat}
    (x : Data.LLVM.Int w) : Data.LLVM.Int.and x (.val (BitVec.allOnes w)) ⊒ x := by
  grind

private theorem Data.LLVM.Int.or_zero_refines {w : Nat}
    (x : Data.LLVM.Int w) : Data.LLVM.Int.or x (.val 0) ⊒ x := by
  grind

private theorem Data.LLVM.Int.or_allOnes_refines {w : Nat}
    (x : Data.LLVM.Int w) :
    Data.LLVM.Int.or x (.val (BitVec.allOnes w)) ⊒ .val (BitVec.allOnes w) := by
  grind

private theorem Data.LLVM.Int.or_zero_flags_refines {w : Nat}
    (x : Data.LLVM.Int w) (disjoint : Bool) :
    Data.LLVM.Int.or x (.val 0) disjoint ⊒ x := by
  grind

private theorem Data.LLVM.Int.or_allOnes_flags_refines {w : Nat}
    (x : Data.LLVM.Int w) (disjoint : Bool) :
    Data.LLVM.Int.or x (.val (BitVec.allOnes w)) disjoint ⊒
      .val (BitVec.allOnes w) := by
  grind

private theorem Data.LLVM.Int.xor_zero_refines {w : Nat}
    (x : Data.LLVM.Int w) : Data.LLVM.Int.xor x (.val 0) ⊒ x := by
  grind

private theorem Data.LLVM.Int.shl_zero_refines {w : Nat}
    (x : Data.LLVM.Int w) (nsw nuw : Bool) :
    Data.LLVM.Int.shl x (.val 0) nsw nuw ⊒ x := by
  grind

private theorem Data.LLVM.Int.lshr_zero_refines {w : Nat}
    (x : Data.LLVM.Int w) (exact : Bool) :
    Data.LLVM.Int.lshr x (.val 0) exact ⊒ x := by
  grind

private theorem Data.LLVM.Int.ashr_zero_refines {w : Nat}
    (x : Data.LLVM.Int w) (exact : Bool) :
    Data.LLVM.Int.ashr x (.val 0) exact ⊒ x := by
  grind

private theorem Data.LLVM.Byte.shl_eq_local {w : Nat} (x : Data.LLVM.Byte w)
    (y : Data.LLVM.Int w) (nuw : Bool) :
    x.shl y nuw =
      if y.isPoison || y.getValueD ≥ w then Data.LLVM.Byte.allPoison
      else if nuw ∧ (x.val <<< y.getValueD) >>> y.getValueD ≠ x.val then
        Data.LLVM.Byte.allPoison
      else if nuw ∧ (x.poison <<< y.getValueD) >>> y.getValueD ≠ x.poison then
        Data.LLVM.Byte.allPoison
      else ⟨x.val <<< y.getValueD, x.poison <<< y.getValueD, by
        simp [← BitVec.shiftLeft_and_distrib, x.h]⟩ := by
  cases y with
  | poison => simp [Data.LLVM.Byte.shl, Id.run, Data.LLVM.Int.isPoison_of_poison]
  | val y' =>
    simp only [Data.LLVM.Byte.shl, Id.run, Data.LLVM.Int.isPoison_of_val,
      Data.LLVM.Int.getValueD_val, Bool.false_or, decide_eq_true_eq]
    repeat' split
    all_goals first | rfl | simp_all | (exfalso; bv_omega)

private theorem BitVec.ofNat_self_ne_zero {n : Nat} (hPos : 0 < n) :
    BitVec.ofNat n n ≠ 0 := by
  intro h
  have hLt : n < 2 ^ n := Nat.lt_two_pow_self
  have hNat := congrArg BitVec.toNat h
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hLt] at hNat
  omega

@[grind .] private theorem Data.LLVM.Byte.shl_zero_refines {w : Nat}
    (x : Data.LLVM.Byte w) (nuw : Bool) :
    Data.LLVM.Byte.shl x (.val 0) nuw ⊒ x := by
  cases w with
  | zero =>
    cases x with
    | mk val poison h =>
      have hVal : val = 0 := Subsingleton.elim _ _
      have hPoison : poison = 0 := Subsingleton.elim _ _
      subst val
      subst poison
      simp [Data.LLVM.Byte.shl_eq_local, Data.LLVM.Byte.isRefinedBy,
        Data.LLVM.Byte.allPoison]
  | succ w =>
    have hNonzero : BitVec.ofNat (w + 1) (w + 1) ≠ 0 :=
      BitVec.ofNat_self_ne_zero (by omega)
    simp [Data.LLVM.Byte.shl_eq_local, Data.LLVM.Byte.isRefinedBy]
    split
    · contradiction
    · exact Data.LLVM.Byte.isRefinedBy_refl x

@[grind .] private theorem Data.LLVM.Byte.lshr_zero_refines {w : Nat}
    (x : Data.LLVM.Byte w) (exact : Bool) :
    Data.LLVM.Byte.lshr x (.val 0) exact ⊒ x := by
  cases w with
  | zero =>
    cases x with
    | mk val poison h =>
      have hVal : val = 0 := Subsingleton.elim _ _
      have hPoison : poison = 0 := Subsingleton.elim _ _
      subst val
      subst poison
      simp [Data.LLVM.Byte.lshr, Data.LLVM.Byte.isRefinedBy,
        Data.LLVM.Byte.allPoison]
  | succ w =>
    have hNonzero : BitVec.ofNat (w + 1) (w + 1) ≠ 0 :=
      BitVec.ofNat_self_ne_zero (by omega)
    simp [Data.LLVM.Byte.lshr, Data.LLVM.Byte.isRefinedBy]
    split
    · contradiction
    · exact Data.LLVM.Byte.isRefinedBy_refl x

theorem Arith.addZero_refines
    (properties : HasDialectOpInfo.propertiesOf Arith.addi)
    (resultTypes : Array TypeAttr) (actualOperands : Array RuntimeValue) {bw : Nat}
    (hAgree : ConstOperands.Agree #[none, some (.int bw (.val 0))] actualOperands) :
    FoldOutcome.Refines (.operand 0) (.arith .addi) properties resultTypes actualOperands := by
  rcases properties with ⟨⟨nsw, nuw⟩⟩
  obtain ⟨lhs, rfl⟩ := hAgree.binaryIntShape
  cases lhs with
  | int lhsBw lhs =>
    by_cases hBw : bw = lhsBw
    · subst lhsBw
      cases lhs with
      | val value =>
        simp [FoldOutcome.Refines, FoldOutcome.target, foldEvaluate, Veir.interpretOp',
          Arith.interpretOp', Interp.isRefinedBy,
          RuntimeValue.arrayIsRefinedBy, RuntimeValue.isRefinedBy,
          isRefinedBy]
        exact Data.LLVM.Int.add_zero_refines _ _ _
      | poison =>
        simp [FoldOutcome.Refines, FoldOutcome.target, foldEvaluate, Veir.interpretOp',
          Arith.interpretOp', Interp.isRefinedBy,
          RuntimeValue.arrayIsRefinedBy, RuntimeValue.isRefinedBy]
        exact Data.LLVM.Int.add_zero_refines _ _ _
    · simp [FoldOutcome.Refines, FoldOutcome.target, foldEvaluate, Veir.interpretOp',
        Arith.interpretOp', hBw, Interp.isRefinedBy]
  | byte | addr | reg | float =>
    simp [FoldOutcome.Refines, FoldOutcome.target, foldEvaluate, Veir.interpretOp',
      Arith.interpretOp', Interp.isRefinedBy]

theorem Arith.subZero_refines
    (properties : HasDialectOpInfo.propertiesOf Arith.subi)
    (resultTypes : Array TypeAttr) (actualOperands : Array RuntimeValue) {bw : Nat}
    (hAgree : ConstOperands.Agree #[none, some (.int bw (.val 0))] actualOperands) :
    FoldOutcome.Refines (.operand 0) (.arith .subi) properties resultTypes actualOperands := by
  obtain ⟨lhs, rfl⟩ := hAgree.binaryIntShape
  rcases properties with ⟨⟨nsw, nuw⟩⟩
  cases lhs with
  | int lhsBw lhs =>
    by_cases hBw : bw = lhsBw
    · subst lhsBw
      simp [FoldOutcome.Refines, FoldOutcome.target, foldEvaluate, Veir.interpretOp',
        Arith.interpretOp', Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy,
        RuntimeValue.isRefinedBy]
      exact Data.LLVM.Int.sub_zero_refines lhs nsw nuw
    · simp [FoldOutcome.Refines, FoldOutcome.target, foldEvaluate, Veir.interpretOp',
        Arith.interpretOp', hBw, Interp.isRefinedBy]
  | byte | addr | reg | float =>
    simp [FoldOutcome.Refines, FoldOutcome.target, foldEvaluate, Veir.interpretOp',
      Arith.interpretOp', Interp.isRefinedBy]

inductive Arith.PartialFold :
    (op : Arith) → (bw : Nat) → Data.LLVM.Int bw → FoldOutcome → Prop where
  | addZero : PartialFold .addi bw (.val 0) (.operand 0)
  | subZero : PartialFold .subi bw (.val 0) (.operand 0)
  | mulZero : PartialFold .muli bw (.val 0) (.constant (.int bw (.val 0)))
  | mulOne : PartialFold .muli bw (.val 1) (.operand 0)
  | andZero : PartialFold .andi bw (.val 0) (.constant (.int bw (.val 0)))
  | andAllOnes : PartialFold .andi bw (.val (BitVec.allOnes bw)) (.operand 0)
  | orZero : PartialFold .ori bw (.val 0) (.operand 0)
  | orAllOnes : PartialFold .ori bw (.val (BitVec.allOnes bw))
      (.constant (.int bw (.val (BitVec.allOnes bw))))
  | xorZero : PartialFold .xori bw (.val 0) (.operand 0)
  | shlZero : PartialFold .shli bw (.val 0) (.operand 0)
  | ashrZero : PartialFold .shrsi bw (.val 0) (.operand 0)
  | lshrZero : PartialFold .shrui bw (.val 0) (.operand 0)
  | sdivZero : PartialFold .divsi bw (.val 0) (.constant (.int bw .poison))
  | udivZero : PartialFold .divui bw (.val 0) (.constant (.int bw .poison))
  | sremZero : PartialFold .remsi bw (.val 0) (.constant (.int bw .poison))
  | uremZero : PartialFold .remui bw (.val 0) (.constant (.int bw .poison))

theorem Arith.partialFold_refines {op : Arith} {bw : Nat}
    {rhs : Data.LLVM.Int bw} {outcome : FoldOutcome}
    (rule : Arith.PartialFold op bw rhs outcome)
    (properties : HasDialectOpInfo.propertiesOf op)
    (resultTypes : Array TypeAttr) (actualOperands : Array RuntimeValue)
    (hAgree : ConstOperands.Agree #[none, some (.int bw rhs)] actualOperands) :
    FoldOutcome.Refines outcome (.arith op) properties resultTypes actualOperands := by
  cases rule <;> obtain ⟨lhs, rfl⟩ := hAgree.binaryIntShape
  all_goals
    cases lhs with
    | int lhsBw lhs =>
      by_cases hBw : bw = lhsBw
      · subst lhsBw
        simp [FoldOutcome.Refines, FoldOutcome.target, foldEvaluate, Veir.interpretOp',
          Arith.interpretOp', Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy,
          RuntimeValue.isRefinedBy, Interp.ub] <;> grind
      · simp [FoldOutcome.Refines, FoldOutcome.target, foldEvaluate, Veir.interpretOp',
          Arith.interpretOp', hBw, Interp.isRefinedBy]
    | byte | addr | reg | float =>
      simp [FoldOutcome.Refines, FoldOutcome.target, foldEvaluate, Veir.interpretOp',
        Arith.interpretOp', Interp.isRefinedBy]

theorem Arith.dispatchPartialFold {op : Arith} {bw : Nat}
    {rhs expected : BitVec bw} {known₀ : Option RuntimeValue}
    {outcome expectedOutcome : FoldOutcome}
    (rule : Arith.PartialFold op bw (.val expected) expectedOutcome)
    (properties : HasDialectOpInfo.propertiesOf op)
    (knownOperands : Array (Option RuntimeValue))
    (resultTypes : Array TypeAttr) (actualOperands : Array RuntimeValue)
    (hList : knownOperands.toList = [known₀, some (.int bw (.val rhs))])
    (hRhs : rhs = expected) (hOutcome : expectedOutcome = outcome)
    (hAgree : ConstOperands.Agree knownOperands actualOperands) :
    FoldOutcome.Refines outcome (.arith op) properties resultTypes actualOperands := by
  subst outcome
  exact Arith.partialFold_refines rule properties resultTypes actualOperands
    (hAgree.rhsInt_of_toList hList (congrArg Data.LLVM.Int.val hRhs))

theorem Arith.foldsTo_refines (op : Arith)
    (properties : HasDialectOpInfo.propertiesOf op)
    (knownOperands : Array (Option RuntimeValue)) (outcome : FoldOutcome)
    (resultTypes : Array TypeAttr) (actualOperands : Array RuntimeValue)
    (hFold : Arith.foldsTo op properties resultTypes knownOperands = some outcome)
    (hAgree : ConstOperands.Agree knownOperands actualOperands) :
    FoldOutcome.Refines outcome (.arith op) properties resultTypes actualOperands := by
  cases op <;> simp only [Arith.foldsTo] at hFold
  all_goals try contradiction
  case addi =>
    split at hFold <;> simp_all
    rename_i _ known₀ bw rhs hList
    obtain ⟨hRhs, hOutcome⟩ := hFold
    exact Arith.dispatchPartialFold (rhs := 0) (expected := 0) (.addZero) properties knownOperands resultTypes
      actualOperands hList rfl hOutcome hAgree
  case subi =>
    split at hFold <;> simp_all
    rename_i _ known₀ bw rhs hList
    exact Arith.dispatchPartialFold (rhs := 0) (expected := 0) (.subZero) properties knownOperands resultTypes
      actualOperands hList rfl hFold.2 hAgree
  case xori =>
    split at hFold <;> simp_all
    rename_i _ known₀ bw rhs hList
    exact Arith.dispatchPartialFold (rhs := 0) (expected := 0) (.xorZero) properties knownOperands resultTypes
      actualOperands hList rfl hFold.2 hAgree
  case shli =>
    split at hFold <;> simp_all
    rename_i _ known₀ bw rhs hList
    exact Arith.dispatchPartialFold (rhs := 0) (expected := 0) (.shlZero) properties knownOperands resultTypes
      actualOperands hList rfl hFold.2 hAgree
  case shrsi =>
    split at hFold <;> simp_all
    rename_i _ known₀ bw rhs hList
    exact Arith.dispatchPartialFold (rhs := 0) (expected := 0) (.ashrZero) properties knownOperands resultTypes
      actualOperands hList rfl hFold.2 hAgree
  case shrui =>
    split at hFold <;> simp_all
    rename_i _ known₀ bw rhs hList
    exact Arith.dispatchPartialFold (rhs := 0) (expected := 0) (.lshrZero) properties knownOperands resultTypes
      actualOperands hList rfl hFold.2 hAgree
  case divsi =>
    split at hFold <;> simp_all
    rename_i _ known₀ bw rhs hList
    exact Arith.dispatchPartialFold (rhs := 0) (expected := 0) (.sdivZero) properties knownOperands resultTypes
      actualOperands hList rfl hFold.2 hAgree
  case divui =>
    split at hFold <;> simp_all
    rename_i _ known₀ bw rhs hList
    exact Arith.dispatchPartialFold (rhs := 0) (expected := 0) (.udivZero) properties knownOperands resultTypes
      actualOperands hList rfl hFold.2 hAgree
  case remsi =>
    split at hFold <;> simp_all
    rename_i _ known₀ bw rhs hList
    exact Arith.dispatchPartialFold (rhs := 0) (expected := 0) (.sremZero) properties knownOperands resultTypes
      actualOperands hList rfl hFold.2 hAgree
  case remui =>
    split at hFold <;> simp_all
    rename_i _ known₀ bw rhs hList
    exact Arith.dispatchPartialFold (rhs := 0) (expected := 0) (.uremZero) properties knownOperands resultTypes
      actualOperands hList rfl hFold.2 hAgree
  case muli =>
    split at hFold <;> simp_all
    rename_i _ known₀ bw rhs hList
    split at hFold
    next hFirst =>
      exact Arith.dispatchPartialFold (.mulZero) properties knownOperands resultTypes
        actualOperands hList hFirst (Option.some.inj hFold) hAgree
    next hNotFirst =>
      split at hFold
      next hSecond =>
        exact Arith.dispatchPartialFold (.mulOne) properties knownOperands resultTypes
          actualOperands hList hSecond (Option.some.inj hFold) hAgree
      next hNotSecond => contradiction
  case andi =>
    split at hFold <;> simp_all
    rename_i _ known₀ bw rhs hList
    split at hFold
    next hZero =>
      exact Arith.dispatchPartialFold (.andZero) properties knownOperands resultTypes
        actualOperands hList hZero (Option.some.inj hFold) hAgree
    next hNotZero =>
      split at hFold
      next hAllOnes =>
        exact Arith.dispatchPartialFold (.andAllOnes) properties knownOperands resultTypes
          actualOperands hList hAllOnes (Option.some.inj hFold) hAgree
      next hNotAllOnes => contradiction
  case ori =>
    split at hFold <;> simp_all
    rename_i _ known₀ bw rhs hList
    split at hFold
    next hZero =>
      exact Arith.dispatchPartialFold (.orZero) properties knownOperands resultTypes
        actualOperands hList hZero (Option.some.inj hFold) hAgree
    next hNotZero =>
      split at hFold
      next hAllOnes =>
        exact Arith.dispatchPartialFold (.orAllOnes) properties knownOperands resultTypes
          actualOperands hList hAllOnes (Option.some.inj hFold) hAgree
      next hNotAllOnes => contradiction

theorem OpCode.foldsTo_arith_refines (op : Arith)
    (properties : HasDialectOpInfo.propertiesOf op)
    (knownOperands : Array (Option RuntimeValue)) (outcome : FoldOutcome)
    (resultTypes : Array TypeAttr) (actualOperands : Array RuntimeValue)
    (hFold : OpCode.foldsTo (.arith op) properties resultTypes knownOperands = some outcome)
    (hAgree : ConstOperands.Agree knownOperands actualOperands) :
    FoldOutcome.Refines outcome (.arith op) properties resultTypes actualOperands := by
  unfold OpCode.foldsTo at hFold
  split at hFold
  · injection hFold with hOutcome
    subst outcome
    exact FoldOutcome.evaluate_refines (.arith op) properties resultTypes actualOperands
  · exact Arith.foldsTo_refines op properties knownOperands outcome resultTypes
      actualOperands hFold hAgree

theorem Arith.foldDecision_refines (op : Arith)
    (properties : HasDialectOpInfo.propertiesOf op)
    (knownOperands : Array (Option RuntimeValue))
    (resultTypes : Array TypeAttr) (actualOperands : Array RuntimeValue)
    (hAgree : ConstOperands.Agree knownOperands actualOperands) :
    FoldDecision.Refines
      (foldDecision (.arith op) properties resultTypes knownOperands)
      (.arith op) properties resultTypes actualOperands := by
  apply FoldDecision.refines_of_foldsTo_refines (.arith op) properties knownOperands
    resultTypes actualOperands hAgree
  intro outcome hFold
  exact OpCode.foldsTo_arith_refines op properties knownOperands outcome resultTypes
    actualOperands hFold hAgree

/-! ## LLVM partial folds -/

inductive Llvm.PartialFold :
    (op : Llvm) → (bw : Nat) → Data.LLVM.Int bw → FoldOutcome → Prop where
  | addZero : PartialFold .add bw (.val 0) (.operand 0)
  | subZero : PartialFold .sub bw (.val 0) (.operand 0)
  | mulZero : PartialFold .mul bw (.val 0) (.constant (.int bw (.val 0)))
  | mulOne : PartialFold .mul bw (.val 1) (.operand 0)
  | andZero : PartialFold .and bw (.val 0) (.constant (.int bw (.val 0)))
  | andAllOnes : PartialFold .and bw (.val (BitVec.allOnes bw)) (.operand 0)
  | orZero : PartialFold .or bw (.val 0) (.operand 0)
  | orAllOnes : PartialFold .or bw (.val (BitVec.allOnes bw))
      (.constant (.int bw (.val (BitVec.allOnes bw))))
  | xorZero : PartialFold .xor bw (.val 0) (.operand 0)
  | shlZero : PartialFold .shl bw (.val 0) (.operand 0)
  | lshrZero : PartialFold .lshr bw (.val 0) (.operand 0)
  | ashrZero : PartialFold .ashr bw (.val 0) (.operand 0)
  | sdivZero : PartialFold .sdiv bw (.val 0) (.constant (.int bw .poison))
  | udivZero : PartialFold .udiv bw (.val 0) (.constant (.int bw .poison))
  | sremZero : PartialFold .srem bw (.val 0) (.constant (.int bw .poison))
  | uremZero : PartialFold .urem bw (.val 0) (.constant (.int bw .poison))

theorem Llvm.partialFold_refines {op : Llvm} {bw : Nat}
    {rhs : Data.LLVM.Int bw} {outcome : FoldOutcome}
    (rule : Llvm.PartialFold op bw rhs outcome)
    (properties : HasDialectOpInfo.propertiesOf op)
    (resultTypes : Array TypeAttr) (actualOperands : Array RuntimeValue)
    (hAgree : ConstOperands.Agree #[none, some (.int bw rhs)] actualOperands) :
    FoldOutcome.Refines outcome (.llvm op) properties resultTypes actualOperands := by
  cases rule <;> obtain ⟨lhs, rfl⟩ := hAgree.binaryIntShape
  all_goals
    cases lhs with
    | int lhsBw lhs =>
      by_cases hBw : bw = lhsBw
      · subst lhsBw
        simp [FoldOutcome.Refines, FoldOutcome.target, foldEvaluate, Veir.interpretOp',
          Llvm.interpretOp', Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy,
          RuntimeValue.isRefinedBy, Interp.ub] <;> grind
      · simp [FoldOutcome.Refines, FoldOutcome.target, foldEvaluate, Veir.interpretOp',
          Llvm.interpretOp', hBw, Interp.isRefinedBy]
    | byte lhsBw lhs =>
      by_cases hBw : bw = lhsBw
      · subst lhsBw
        first
        | by_cases hNsw : properties.nsw = true
          · simp [FoldOutcome.Refines, FoldOutcome.target, foldEvaluate,
              Veir.interpretOp', Llvm.interpretOp', Interp.isRefinedBy, hNsw]
          · simp [FoldOutcome.Refines, FoldOutcome.target, foldEvaluate,
              Veir.interpretOp', Llvm.interpretOp', Interp.isRefinedBy,
              RuntimeValue.arrayIsRefinedBy, RuntimeValue.isRefinedBy, hNsw]
            exact Data.LLVM.Byte.shl_zero_refines lhs properties.nuw
        | simp [FoldOutcome.Refines, FoldOutcome.target, foldEvaluate,
            Veir.interpretOp', Llvm.interpretOp', Interp.isRefinedBy,
            RuntimeValue.arrayIsRefinedBy, RuntimeValue.isRefinedBy]
          exact Data.LLVM.Byte.lshr_zero_refines lhs properties.exact
        | simp [FoldOutcome.Refines, FoldOutcome.target, foldEvaluate,
            Veir.interpretOp', Llvm.interpretOp', Interp.isRefinedBy]
      · simp [FoldOutcome.Refines, FoldOutcome.target, foldEvaluate, Veir.interpretOp',
          Llvm.interpretOp', hBw, Interp.isRefinedBy]
    | addr | reg | float =>
      simp [FoldOutcome.Refines, FoldOutcome.target, foldEvaluate, Veir.interpretOp',
        Llvm.interpretOp', Interp.isRefinedBy]

theorem Llvm.dispatchPartialFold {op : Llvm} {bw : Nat}
    {rhs expected : BitVec bw} {known₀ : Option RuntimeValue}
    {outcome expectedOutcome : FoldOutcome}
    (rule : Llvm.PartialFold op bw (.val expected) expectedOutcome)
    (properties : HasDialectOpInfo.propertiesOf op)
    (knownOperands : Array (Option RuntimeValue))
    (resultTypes : Array TypeAttr) (actualOperands : Array RuntimeValue)
    (hList : knownOperands.toList = [known₀, some (.int bw (.val rhs))])
    (hRhs : rhs = expected) (hOutcome : expectedOutcome = outcome)
    (hAgree : ConstOperands.Agree knownOperands actualOperands) :
    FoldOutcome.Refines outcome (.llvm op) properties resultTypes actualOperands := by
  subst outcome
  exact Llvm.partialFold_refines rule properties resultTypes actualOperands
    (hAgree.rhsInt_of_toList hList (congrArg Data.LLVM.Int.val hRhs))

theorem Llvm.foldsTo_refines (op : Llvm)
    (properties : HasDialectOpInfo.propertiesOf op)
    (knownOperands : Array (Option RuntimeValue)) (outcome : FoldOutcome)
    (resultTypes : Array TypeAttr) (actualOperands : Array RuntimeValue)
    (hFold : Llvm.foldsTo op properties resultTypes knownOperands = some outcome)
    (hAgree : ConstOperands.Agree knownOperands actualOperands) :
    FoldOutcome.Refines outcome (.llvm op) properties resultTypes actualOperands := by
  cases op <;> simp only [Llvm.foldsTo] at hFold
  all_goals try contradiction
  case add =>
    split at hFold <;> simp_all
    rename_i _ known₀ bw rhs hList
    exact Llvm.dispatchPartialFold (rhs := 0) (expected := 0) (.addZero)
      properties knownOperands resultTypes actualOperands hList rfl hFold.2 hAgree
  case sub =>
    split at hFold <;> simp_all
    rename_i _ known₀ bw rhs hList
    exact Llvm.dispatchPartialFold (rhs := 0) (expected := 0) (.subZero)
      properties knownOperands resultTypes actualOperands hList rfl hFold.2 hAgree
  case xor =>
    split at hFold <;> simp_all
    rename_i _ known₀ bw rhs hList
    exact Llvm.dispatchPartialFold (rhs := 0) (expected := 0) (.xorZero)
      properties knownOperands resultTypes actualOperands hList rfl hFold.2 hAgree
  case shl =>
    split at hFold <;> simp_all
    rename_i _ known₀ bw rhs hList
    exact Llvm.dispatchPartialFold (rhs := 0) (expected := 0) (.shlZero)
      properties knownOperands resultTypes actualOperands hList rfl hFold.2 hAgree
  case lshr =>
    split at hFold <;> simp_all
    rename_i _ known₀ bw rhs hList
    exact Llvm.dispatchPartialFold (rhs := 0) (expected := 0) (.lshrZero)
      properties knownOperands resultTypes actualOperands hList rfl hFold.2 hAgree
  case ashr =>
    split at hFold <;> simp_all
    rename_i _ known₀ bw rhs hList
    exact Llvm.dispatchPartialFold (rhs := 0) (expected := 0) (.ashrZero)
      properties knownOperands resultTypes actualOperands hList rfl hFold.2 hAgree
  case sdiv =>
    split at hFold <;> simp_all
    rename_i _ known₀ bw rhs hList
    exact Llvm.dispatchPartialFold (rhs := 0) (expected := 0) (.sdivZero)
      properties knownOperands resultTypes actualOperands hList rfl hFold.2 hAgree
  case udiv =>
    split at hFold <;> simp_all
    rename_i _ known₀ bw rhs hList
    exact Llvm.dispatchPartialFold (rhs := 0) (expected := 0) (.udivZero)
      properties knownOperands resultTypes actualOperands hList rfl hFold.2 hAgree
  case srem =>
    split at hFold <;> simp_all
    rename_i _ known₀ bw rhs hList
    exact Llvm.dispatchPartialFold (rhs := 0) (expected := 0) (.sremZero)
      properties knownOperands resultTypes actualOperands hList rfl hFold.2 hAgree
  case urem =>
    split at hFold <;> simp_all
    rename_i _ known₀ bw rhs hList
    exact Llvm.dispatchPartialFold (rhs := 0) (expected := 0) (.uremZero)
      properties knownOperands resultTypes actualOperands hList rfl hFold.2 hAgree
  case mul =>
    split at hFold <;> simp_all
    rename_i _ known₀ bw rhs hList
    split at hFold
    next hZero =>
      exact Llvm.dispatchPartialFold (.mulZero) properties knownOperands resultTypes
        actualOperands hList hZero (Option.some.inj hFold) hAgree
    next hNotZero =>
      split at hFold
      next hOne =>
        exact Llvm.dispatchPartialFold (.mulOne) properties knownOperands resultTypes
          actualOperands hList hOne (Option.some.inj hFold) hAgree
      next hNotOne => contradiction
  case and =>
    split at hFold <;> simp_all
    rename_i _ known₀ bw rhs hList
    split at hFold
    next hZero =>
      exact Llvm.dispatchPartialFold (.andZero) properties knownOperands resultTypes
        actualOperands hList hZero (Option.some.inj hFold) hAgree
    next hNotZero =>
      split at hFold
      next hAllOnes =>
        exact Llvm.dispatchPartialFold (.andAllOnes) properties knownOperands resultTypes
          actualOperands hList hAllOnes (Option.some.inj hFold) hAgree
      next hNotAllOnes => contradiction
  case or =>
    split at hFold <;> simp_all
    rename_i _ known₀ bw rhs hList
    split at hFold
    next hZero =>
      exact Llvm.dispatchPartialFold (.orZero) properties knownOperands resultTypes
        actualOperands hList hZero (Option.some.inj hFold) hAgree
    next hNotZero =>
      split at hFold
      next hAllOnes =>
        exact Llvm.dispatchPartialFold (.orAllOnes) properties knownOperands resultTypes
          actualOperands hList hAllOnes (Option.some.inj hFold) hAgree
      next hNotAllOnes => contradiction

theorem OpCode.foldsTo_llvm_refines (op : Llvm)
    (properties : HasDialectOpInfo.propertiesOf op)
    (knownOperands : Array (Option RuntimeValue)) (outcome : FoldOutcome)
    (resultTypes : Array TypeAttr) (actualOperands : Array RuntimeValue)
    (hFold : OpCode.foldsTo (.llvm op) properties resultTypes knownOperands = some outcome)
    (hAgree : ConstOperands.Agree knownOperands actualOperands) :
    FoldOutcome.Refines outcome (.llvm op) properties resultTypes actualOperands := by
  unfold OpCode.foldsTo at hFold
  split at hFold
  · injection hFold with hOutcome
    subst outcome
    exact FoldOutcome.evaluate_refines (.llvm op) properties resultTypes actualOperands
  · exact Llvm.foldsTo_refines op properties knownOperands outcome resultTypes
      actualOperands hFold hAgree

theorem Llvm.foldDecision_refines (op : Llvm)
    (properties : HasDialectOpInfo.propertiesOf op)
    (knownOperands : Array (Option RuntimeValue))
    (resultTypes : Array TypeAttr) (actualOperands : Array RuntimeValue)
    (hAgree : ConstOperands.Agree knownOperands actualOperands) :
    FoldDecision.Refines
      (foldDecision (.llvm op) properties resultTypes knownOperands)
      (.llvm op) properties resultTypes actualOperands := by
  apply FoldDecision.refines_of_foldsTo_refines (.llvm op) properties knownOperands
    resultTypes actualOperands hAgree
  intro outcome hFold
  exact OpCode.foldsTo_llvm_refines op properties knownOperands outcome resultTypes
    actualOperands hFold hAgree

/-! ## RISC-V partial folds -/

/-- Operand-returning binary rules in the RISC-V fold table. -/
inductive Riscv.BinaryOperandFold : Riscv → BitVec 64 → Prop where
  | addZero : BinaryOperandFold .add 0
  | subZero : BinaryOperandFold .sub 0
  | xorZero : BinaryOperandFold .xor 0
  | orZero : BinaryOperandFold .or 0
  | andAllOnes : BinaryOperandFold .and (BitVec.allOnes 64)
  | mulOne : BinaryOperandFold .mul 1
  | sllZero : BinaryOperandFold .sll 0
  | srlZero : BinaryOperandFold .srl 0
  | sraZero : BinaryOperandFold .sra 0

/-- Constant-returning binary rules in the RISC-V fold table. -/
inductive Riscv.BinaryConstantFold : Riscv → BitVec 64 → BitVec 64 → Prop where
  | orAllOnes : BinaryConstantFold .or (BitVec.allOnes 64) (BitVec.allOnes 64)
  | andZero : BinaryConstantFold .and 0 0
  | mulZero : BinaryConstantFold .mul 0 0

theorem ConstOperands.Agree.binaryRegShape {rhs : BitVec 64}
    {actualOperands : Array RuntimeValue}
    (hAgree : ConstOperands.Agree
      #[none, some (.reg (Data.RISCV.li rhs))] actualOperands) :
    ∃ lhs, actualOperands = #[lhs, .reg (Data.RISCV.li rhs)] := by
  let lhs := actualOperands[0]!
  have hShape : actualOperands = #[lhs, actualOperands[1]!] := hAgree.pair.1
  have hRhs : RuntimeValue.reg (Data.RISCV.li rhs) = actualOperands[1]! := hAgree.pair.2.2
  exact ⟨lhs, hShape.trans (by rw [← hRhs])⟩

/-- Every operand-returning binary RISC-V fold rule is sound. -/
theorem Riscv.binaryOperandFold_refines {op : Riscv} {rhs : BitVec 64}
    (rule : Riscv.BinaryOperandFold op rhs)
    (properties : HasDialectOpInfo.propertiesOf op)
    (resultTypes : Array TypeAttr) (actualOperands : Array RuntimeValue)
    (hAgree : ConstOperands.Agree
      #[none, some (.reg (Data.RISCV.li rhs))] actualOperands) :
    FoldOutcome.Refines (.operand 0) (.riscv op) properties resultTypes actualOperands := by
  cases rule
  all_goals
    obtain ⟨lhs, rfl⟩ := hAgree.binaryRegShape
    cases lhs <;>
      simp [FoldOutcome.Refines, FoldOutcome.target, foldEvaluate, Veir.interpretOp',
        Riscv.interpretOp', Data.RISCV.add, Data.RISCV.sub, Data.RISCV.xor,
        Data.RISCV.or, Data.RISCV.and, Data.RISCV.mul, Data.RISCV.sll,
        Data.RISCV.srl, Data.RISCV.sra, Data.RISCV.li, Interp.isRefinedBy,
        RuntimeValue.arrayIsRefinedBy, RuntimeValue.isRefinedBy] <;> bv_decide

/-- Every constant-returning binary RISC-V fold rule is sound. -/
theorem Riscv.binaryConstantFold_refines {op : Riscv} {rhs result : BitVec 64}
    (rule : Riscv.BinaryConstantFold op rhs result)
    (properties : HasDialectOpInfo.propertiesOf op)
    (resultTypes : Array TypeAttr) (actualOperands : Array RuntimeValue)
    (hAgree : ConstOperands.Agree
      #[none, some (.reg (Data.RISCV.li rhs))] actualOperands) :
    FoldOutcome.Refines (.constant (.reg (Data.RISCV.li result)))
      (.riscv op) properties resultTypes actualOperands := by
  cases rule
  all_goals
    obtain ⟨lhs, rfl⟩ := hAgree.binaryRegShape
    cases lhs <;>
      simp [FoldOutcome.Refines, FoldOutcome.target, foldEvaluate, Veir.interpretOp',
        Riscv.interpretOp', Data.RISCV.or, Data.RISCV.and, Data.RISCV.mul,
        Data.RISCV.li, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy,
        RuntimeValue.isRefinedBy] <;> bv_decide

/-- Immediate rules in the RISC-V fold table, including their side conditions. -/
inductive Riscv.ImmediateFold :
    (op : Riscv) → HasDialectOpInfo.propertiesOf op → FoldOutcome → Prop where
  | addiZero (properties : HasDialectOpInfo.propertiesOf Riscv.addi)
      (hZero : properties.value.value = 0) :
      ImmediateFold .addi properties (.operand 0)
  | oriZero (properties : HasDialectOpInfo.propertiesOf Riscv.ori)
      (hZero : properties.value.value = 0) :
      ImmediateFold .ori properties (.operand 0)
  | xoriZero (properties : HasDialectOpInfo.propertiesOf Riscv.xori)
      (hZero : properties.value.value = 0) :
      ImmediateFold .xori properties (.operand 0)
  | andiZero (properties : HasDialectOpInfo.propertiesOf Riscv.andi)
      (hZero : properties.value.value = 0) :
      ImmediateFold .andi properties (.constant (.reg (Data.RISCV.li 0)))
  | slliZero (properties : HasDialectOpInfo.propertiesOf Riscv.slli)
      (hZero : properties.value.value = 0) :
      ImmediateFold .slli properties (.operand 0)
  | srliZero (properties : HasDialectOpInfo.propertiesOf Riscv.srli)
      (hZero : properties.value.value = 0) :
      ImmediateFold .srli properties (.operand 0)
  | sraiZero (properties : HasDialectOpInfo.propertiesOf Riscv.srai)
      (hZero : properties.value.value = 0) :
      ImmediateFold .srai properties (.operand 0)

/-- Every certified immediate RISC-V fold rule is sound. -/
theorem Riscv.immediateFold_refines {op : Riscv}
    {properties : HasDialectOpInfo.propertiesOf op} {outcome : FoldOutcome}
    (rule : Riscv.ImmediateFold op properties outcome)
    (resultTypes : Array TypeAttr) (actualOperands : Array RuntimeValue)
    (hAgree : ConstOperands.Agree #[none] actualOperands) :
    FoldOutcome.Refines outcome (.riscv op) properties resultTypes actualOperands := by
  cases rule
  all_goals
    let operand := actualOperands[0]!
    have hShape : actualOperands = #[operand] := hAgree.singleton.1
    rw [hShape]
    cases operand <;>
      simp_all [FoldOutcome.Refines, FoldOutcome.target, foldEvaluate, Veir.interpretOp',
        Riscv.interpretOp', Data.RISCV.addi, Data.RISCV.ori, Data.RISCV.xori,
        Data.RISCV.andi, Data.RISCV.slli, Data.RISCV.srli, Data.RISCV.srai,
        Data.RISCV.li, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy]

theorem Riscv.dispatchBinaryOperandFold {op : Riscv} {rhs : BitVec 64}
    {c : Data.RISCV.Reg} {known₀ : Option RuntimeValue} {outcome : FoldOutcome}
    (rule : Riscv.BinaryOperandFold op rhs)
    (properties : HasDialectOpInfo.propertiesOf op)
    (knownOperands : Array (Option RuntimeValue))
    (resultTypes : Array TypeAttr) (actualOperands : Array RuntimeValue)
    (hList : knownOperands.toList = [known₀, some (.reg c)])
    (hRhs : c.val = rhs) (hOutcome : FoldOutcome.operand 0 = outcome)
    (hAgree : ConstOperands.Agree knownOperands actualOperands) :
    FoldOutcome.Refines outcome (.riscv op) properties resultTypes actualOperands := by
  subst outcome
  exact Riscv.binaryOperandFold_refines rule properties resultTypes actualOperands
    (hAgree.rhsReg_of_toList hList hRhs)

theorem Riscv.dispatchBinaryConstantFold {op : Riscv} {rhs result : BitVec 64}
    {c : Data.RISCV.Reg} {known₀ : Option RuntimeValue} {outcome : FoldOutcome}
    (rule : Riscv.BinaryConstantFold op rhs result)
    (properties : HasDialectOpInfo.propertiesOf op)
    (knownOperands : Array (Option RuntimeValue))
    (resultTypes : Array TypeAttr) (actualOperands : Array RuntimeValue)
    (hList : knownOperands.toList = [known₀, some (.reg c)])
    (hRhs : c.val = rhs)
    (hOutcome : FoldOutcome.constant (.reg (Data.RISCV.li result)) = outcome)
    (hAgree : ConstOperands.Agree knownOperands actualOperands) :
    FoldOutcome.Refines outcome (.riscv op) properties resultTypes actualOperands := by
  subst outcome
  exact Riscv.binaryConstantFold_refines rule properties resultTypes actualOperands
    (hAgree.rhsReg_of_toList hList hRhs)

theorem Riscv.dispatchImmediateFold {op : Riscv}
    {properties : HasDialectOpInfo.propertiesOf op} {expected outcome : FoldOutcome}
    {known₀ : Option RuntimeValue}
    (rule : Riscv.ImmediateFold op properties expected)
    (knownOperands : Array (Option RuntimeValue))
    (resultTypes : Array TypeAttr) (actualOperands : Array RuntimeValue)
    (hList : knownOperands.toList = [known₀]) (hOutcome : expected = outcome)
    (hAgree : ConstOperands.Agree knownOperands actualOperands) :
    FoldOutcome.Refines outcome (.riscv op) properties resultTypes actualOperands := by
  subst outcome
  exact Riscv.immediateFold_refines rule resultTypes actualOperands
    (hAgree.forgetSingleton_of_toList hList)

/-- Every partial-fold result returned by the RISC-V fold table is sound. -/
theorem Riscv.foldsTo_refines (op : Riscv)
    (properties : HasDialectOpInfo.propertiesOf op)
    (knownOperands : Array (Option RuntimeValue)) (outcome : FoldOutcome)
    (resultTypes : Array TypeAttr) (actualOperands : Array RuntimeValue)
    (hFold : Riscv.foldsTo op properties resultTypes knownOperands = some outcome)
    (hAgree : ConstOperands.Agree knownOperands actualOperands) :
    FoldOutcome.Refines outcome (.riscv op) properties resultTypes actualOperands := by
  cases op <;> simp only [Riscv.foldsTo] at hFold
  all_goals try contradiction
  case add =>
    split at hFold <;> simp_all
    rename_i _ head c hList
    obtain ⟨hZero, hOutcome⟩ := hFold
    exact Riscv.dispatchBinaryOperandFold .addZero properties knownOperands
      resultTypes actualOperands hList hZero hOutcome hAgree
  case sub =>
    split at hFold <;> simp_all
    rename_i _ head c hList
    obtain ⟨hZero, hOutcome⟩ := hFold
    exact Riscv.dispatchBinaryOperandFold .subZero properties knownOperands
      resultTypes actualOperands hList hZero hOutcome hAgree
  case xor =>
    split at hFold <;> simp_all
    rename_i _ head c hList
    obtain ⟨hZero, hOutcome⟩ := hFold
    exact Riscv.dispatchBinaryOperandFold .xorZero properties knownOperands
      resultTypes actualOperands hList hZero hOutcome hAgree
  case sll =>
    split at hFold <;> simp_all
    rename_i _ head c hList
    obtain ⟨hZero, hOutcome⟩ := hFold
    exact Riscv.dispatchBinaryOperandFold .sllZero properties knownOperands
      resultTypes actualOperands hList hZero hOutcome hAgree
  case srl =>
    split at hFold <;> simp_all
    rename_i _ head c hList
    obtain ⟨hZero, hOutcome⟩ := hFold
    exact Riscv.dispatchBinaryOperandFold .srlZero properties knownOperands
      resultTypes actualOperands hList hZero hOutcome hAgree
  case sra =>
    split at hFold <;> simp_all
    rename_i _ head c hList
    obtain ⟨hZero, hOutcome⟩ := hFold
    exact Riscv.dispatchBinaryOperandFold .sraZero properties knownOperands
      resultTypes actualOperands hList hZero hOutcome hAgree
  case addi =>
    split at hFold <;> simp_all
    rename_i _ head hList
    obtain ⟨hZero, hOutcome⟩ := hFold
    exact Riscv.dispatchImmediateFold (.addiZero properties hZero) knownOperands
      resultTypes actualOperands hList hOutcome hAgree
  case ori =>
    split at hFold <;> simp_all
    rename_i _ head hList
    obtain ⟨hZero, hOutcome⟩ := hFold
    exact Riscv.dispatchImmediateFold (.oriZero properties hZero) knownOperands
      resultTypes actualOperands hList hOutcome hAgree
  case xori =>
    split at hFold <;> simp_all
    rename_i _ head hList
    obtain ⟨hZero, hOutcome⟩ := hFold
    exact Riscv.dispatchImmediateFold (.xoriZero properties hZero) knownOperands
      resultTypes actualOperands hList hOutcome hAgree
  case slli =>
    split at hFold <;> simp_all
    rename_i _ head hList
    obtain ⟨hZero, hOutcome⟩ := hFold
    exact Riscv.dispatchImmediateFold (.slliZero properties hZero) knownOperands
      resultTypes actualOperands hList hOutcome hAgree
  case srli =>
    split at hFold <;> simp_all
    rename_i _ head hList
    obtain ⟨hZero, hOutcome⟩ := hFold
    exact Riscv.dispatchImmediateFold (.srliZero properties hZero) knownOperands
      resultTypes actualOperands hList hOutcome hAgree
  case srai =>
    split at hFold <;> simp_all
    rename_i _ head hList
    obtain ⟨hZero, hOutcome⟩ := hFold
    exact Riscv.dispatchImmediateFold (.sraiZero properties hZero) knownOperands
      resultTypes actualOperands hList hOutcome hAgree
  case andi =>
    split at hFold <;> simp_all
    rename_i _ head hList
    obtain ⟨hZero, hOutcome⟩ := hFold
    exact Riscv.dispatchImmediateFold (.andiZero properties hZero) knownOperands
      resultTypes actualOperands hList hOutcome hAgree
  case or =>
    split at hFold <;> simp_all
    rename_i _ head c hList
    split at hFold
    next hZero =>
      exact Riscv.dispatchBinaryOperandFold .orZero properties knownOperands
        resultTypes actualOperands hList hZero (Option.some.inj hFold) hAgree
    next hNotZero =>
      split at hFold
      next hAllOnes =>
        exact Riscv.dispatchBinaryConstantFold .orAllOnes properties knownOperands
          resultTypes actualOperands hList hAllOnes (Option.some.inj hFold) hAgree
      next hNotAllOnes => contradiction
  case and =>
    split at hFold <;> simp_all
    rename_i _ head c hList
    split at hFold
    next hZero =>
      exact Riscv.dispatchBinaryConstantFold .andZero properties knownOperands
        resultTypes actualOperands hList hZero (Option.some.inj hFold) hAgree
    next hNotZero =>
      split at hFold
      next hAllOnes =>
        exact Riscv.dispatchBinaryOperandFold .andAllOnes properties knownOperands
          resultTypes actualOperands hList hAllOnes (Option.some.inj hFold) hAgree
      next hNotAllOnes => contradiction
  case mul =>
    split at hFold <;> simp_all
    rename_i _ head c hList
    split at hFold
    next hZero =>
      exact Riscv.dispatchBinaryConstantFold .mulZero properties knownOperands
        resultTypes actualOperands hList hZero (Option.some.inj hFold) hAgree
    next hNotZero =>
      split at hFold
      next hOne =>
        exact Riscv.dispatchBinaryOperandFold .mulOne properties knownOperands
          resultTypes actualOperands hList hOne (Option.some.inj hFold) hAgree
      next hNotOne => contradiction

/-- Every fold outcome returned for a RISC-V opcode is sound. -/
theorem OpCode.foldsTo_riscv_refines (op : Riscv)
    (properties : HasDialectOpInfo.propertiesOf op)
    (knownOperands : Array (Option RuntimeValue)) (outcome : FoldOutcome)
    (resultTypes : Array TypeAttr) (actualOperands : Array RuntimeValue)
    (hFold : OpCode.foldsTo (.riscv op) properties resultTypes knownOperands = some outcome)
    (hAgree : ConstOperands.Agree knownOperands actualOperands) :
    FoldOutcome.Refines outcome (.riscv op) properties resultTypes actualOperands := by
  unfold OpCode.foldsTo at hFold
  split at hFold
  · injection hFold with hOutcome
    subst outcome
    exact FoldOutcome.evaluate_refines (.riscv op) properties resultTypes actualOperands
  · exact Riscv.foldsTo_refines op properties knownOperands outcome resultTypes
      actualOperands hFold hAgree

/--
  A non-evaluation RISC-V outcome remains sound after `foldDecision` resolves
  it. This covers every successful partial fold in `Riscv.foldsTo`.
-/
theorem Riscv.foldDecision_partial_refines (op : Riscv)
    (properties : HasDialectOpInfo.propertiesOf op)
    (knownOperands : Array (Option RuntimeValue)) (outcome : FoldOutcome)
    (resultTypes : Array TypeAttr) (actualOperands : Array RuntimeValue)
    (hFold : OpCode.foldsTo (.riscv op) properties resultTypes knownOperands = some outcome)
    (hNotEvaluate : outcome ≠ .evaluate)
    (hAgree : ConstOperands.Agree knownOperands actualOperands) :
    FoldDecision.Refines
      (foldDecision (.riscv op) properties resultTypes knownOperands)
      (.riscv op) properties resultTypes actualOperands := by
  have hSound := OpCode.foldsTo_riscv_refines op properties knownOperands outcome
    resultTypes actualOperands hFold hAgree
  exact FoldDecision.partial_refines (.riscv op) properties knownOperands outcome
    resultTypes actualOperands hFold hNotEvaluate hSound

/-- Every resolved RISC-V fold decision refines interpreting the source operation. -/
theorem Riscv.foldDecision_refines (op : Riscv)
    (properties : HasDialectOpInfo.propertiesOf op)
    (knownOperands : Array (Option RuntimeValue))
    (resultTypes : Array TypeAttr) (actualOperands : Array RuntimeValue)
    (hAgree : ConstOperands.Agree knownOperands actualOperands) :
    FoldDecision.Refines
      (foldDecision (.riscv op) properties resultTypes knownOperands)
      (.riscv op) properties resultTypes actualOperands := by
  apply FoldDecision.refines_of_foldsTo_refines (.riscv op) properties knownOperands
    resultTypes actualOperands hAgree
  intro outcome hFold
  exact OpCode.foldsTo_riscv_refines op properties knownOperands outcome resultTypes
    actualOperands hFold hAgree

/--
  `mod_arith` is uninterpreted, so `foldEvaluate` never succeeds on it and any fold
  decision for it is (vacuously) sound at the `foldEvaluate` level. The semantic
  anchor for `mod_arith` folds is the `mod-arith-to-arith` lowering.
-/
theorem foldEvaluate_mod_arith (op : Mod_Arith)
    (properties : HasOpInfo.propertiesOf (OpCode.mod_arith op))
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) :
    foldEvaluate (OpCode.mod_arith op) properties resultTypes operands = none := by
  cases op <;> rfl

theorem Mod_Arith.foldDecision_refines (op : Mod_Arith)
    (properties : HasDialectOpInfo.propertiesOf op)
    (knownOperands : Array (Option RuntimeValue))
    (resultTypes : Array TypeAttr) (actualOperands : Array RuntimeValue)
    (hAgree : ConstOperands.Agree knownOperands actualOperands) :
    FoldDecision.Refines
      (foldDecision (.mod_arith op) properties resultTypes knownOperands)
      (.mod_arith op) properties resultTypes actualOperands := by
  apply FoldDecision.refines_of_foldsTo_refines (.mod_arith op) properties knownOperands
    resultTypes actualOperands hAgree
  intro outcome hFold
  simp [FoldOutcome.Refines, foldEvaluate_mod_arith, Interp.isRefinedBy]

/-- Every fold decision produced by the executable dispatcher is sound. -/
theorem OpCode.foldDecision_refines (opCode : OpCode)
    (properties : HasOpInfo.propertiesOf opCode)
    (knownOperands : Array (Option RuntimeValue))
    (resultTypes : Array TypeAttr) (actualOperands : Array RuntimeValue)
    (hAgree : ConstOperands.Agree knownOperands actualOperands) :
    FoldDecision.Refines (foldDecision opCode properties resultTypes knownOperands)
      opCode properties resultTypes actualOperands := by
  cases opCode with
  | arith op =>
    exact Arith.foldDecision_refines op properties knownOperands resultTypes
      actualOperands hAgree
  | llvm op =>
    exact Llvm.foldDecision_refines op properties knownOperands resultTypes
      actualOperands hAgree
  | riscv op =>
    exact Riscv.foldDecision_refines op properties knownOperands resultTypes
      actualOperands hAgree
  | mod_arith op =>
    exact Mod_Arith.foldDecision_refines op properties knownOperands resultTypes
      actualOperands hAgree
  | builtin | func | rv64 | test | hw | comb | datapath
  | riscv_stack | riscv_cf | cf =>
    apply FoldDecision.refines_of_foldsTo_refines _ properties knownOperands
      resultTypes actualOperands hAgree
    intro outcome hFold
    unfold OpCode.foldsTo at hFold
    simp [OpCode.isFoldEvaluable] at hFold

end Veir
