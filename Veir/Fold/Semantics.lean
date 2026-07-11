import Veir.Fold
import Veir.Interpreter.Refinement.Lemmas

/-!
  # Semantics of constant folding

  This file states and proves refinement properties of the executable folding
  infrastructure in `Veir.Fold`.  The proofs are layered so that the pure fold
  tables can be checked independently of IR mutation by `PatternRewriter`.

  The remaining layers are:
  * soundness of every partial-fold table entry;
  * agreement between `ValuePtr.constantValue` and interpreted SSA values;
  * correctness of constant materialization; and
  * lifting the decision-level theorem through `foldOperation` and
    `PatternRewriter.createOrFoldOp!`.
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
    (hFold : Riscv.foldsTo op properties knownOperands = some outcome)
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
    (hFold : OpCode.foldsTo (.riscv op) properties knownOperands = some outcome)
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
    (hFold : OpCode.foldsTo (.riscv op) properties knownOperands = some outcome)
    (hNotEvaluate : outcome ≠ .evaluate)
    (hAgree : ConstOperands.Agree knownOperands actualOperands) :
    FoldDecision.Refines
      (foldDecision (.riscv op) properties resultTypes knownOperands)
      (.riscv op) properties resultTypes actualOperands := by
  have hSound := OpCode.foldsTo_riscv_refines op properties knownOperands outcome
    resultTypes actualOperands hFold hAgree
  unfold foldDecision
  split
  · exact FoldDecision.noFold_refines (.riscv op) properties resultTypes actualOperands
  · split
    · exact FoldDecision.noFold_refines (.riscv op) properties resultTypes actualOperands
    · rw [hFold]
      cases outcome with
      | operand j =>
        simpa [FoldDecision.Refines, FoldDecision.target,
          FoldOutcome.Refines, FoldOutcome.target] using hSound
      | constant value =>
        simpa [FoldDecision.Refines, FoldDecision.target,
          FoldOutcome.Refines, FoldOutcome.target] using hSound
      | evaluate => contradiction

end Veir
