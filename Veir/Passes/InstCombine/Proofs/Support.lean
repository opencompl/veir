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
public meta import Lean

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

/-! ## Commutative operand orientations

Rules over commutative nodes are compiled once per operand orientation, selected by the bits of
a `swaps` parameter through `orient`. Rather than proving each orientation separately, the
validity proof keeps the bits symbolic: `orient_eq` selects each operand with an `if`, the
structural checks split on the bits, and the semantic obligation is normalized once, with the
lemmas below showing the commutative operations ignore the orientation.
-/

theorem orient_eq (swaps index : Nat) (a b : Handle OpCode .value) :
    orient swaps index a b =
      #[if swaps.testBit index then b else a, if swaps.testBit index then a else b] := by
  unfold orient; split <;> simp_all

open Lean Elab Tactic Meta in
/-- Generalize each `Nat.testBit` in the goal to a fresh Boolean pattern choice. -/
elab "generalizeSwapBits" : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let bitsRef ← IO.mkRef (#[] : Array Expr)
  target.forEachWhere (fun e => e.isAppOfArity ``Nat.testBit 2 && !e.hasLooseBVars) fun e =>
    bitsRef.modify fun bits => if bits.contains e then bits else bits.push e
  let bits ← bitsRef.get
  let args := bits.mapIdx fun i e => { expr := e, xName? := some (.mkSimple s!"swap{i}") }
  let (_, goal) ← (← getMainGoal).generalize args
  replaceMainGoal [goal]

private theorem int_add_comm {w : Nat} (x y : Data.LLVM.Int w) (nsw nuw : Bool) :
    x.add y nsw nuw = y.add x nsw nuw := by
  cases x <;> cases y <;> simp [Data.LLVM.Int.add, BitVec.add_comm, BitVec.saddOverflow_comm,
    BitVec.uaddOverflow_comm, Id.run]

private theorem int_smax_comm {w : Nat} (x y : Data.LLVM.Int w) : x.smax y = y.smax x := by
  cases x <;> cases y <;> simp only [Data.LLVM.Int.smax, Id.run]
  rename_i a b
  by_cases h₁ : a.sle b <;> by_cases h₂ : b.sle a <;>
    simp only [h₁, h₂, ↓reduceIte, Bool.false_eq_true] <;>
    simp only [BitVec.sle, decide_eq_true_eq, Bool.not_eq_true, decide_eq_false_iff_not] at h₁ h₂
  · congr 1; apply BitVec.eq_of_toInt_eq; omega
  · omega

private theorem int_smin_comm {w : Nat} (x y : Data.LLVM.Int w) : x.smin y = y.smin x := by
  cases x <;> cases y <;> simp only [Data.LLVM.Int.smin, Id.run]
  rename_i a b
  by_cases h₁ : a.sle b <;> by_cases h₂ : b.sle a <;>
    simp only [h₁, h₂, ↓reduceIte, Bool.false_eq_true] <;>
    simp only [BitVec.sle, decide_eq_true_eq, Bool.not_eq_true, decide_eq_false_iff_not] at h₁ h₂
  · congr 1; apply BitVec.eq_of_toInt_eq; omega
  · omega

private theorem int_umax_comm {w : Nat} (x y : Data.LLVM.Int w) : x.umax y = y.umax x := by
  cases x <;> cases y <;> simp only [Data.LLVM.Int.umax, Id.run]
  rename_i a b
  by_cases h₁ : a.ule b <;> by_cases h₂ : b.ule a <;>
    simp only [h₁, h₂, ↓reduceIte, Bool.false_eq_true] <;>
    simp only [BitVec.ule, decide_eq_true_eq, Bool.not_eq_true, decide_eq_false_iff_not] at h₁ h₂
  · congr 1; apply BitVec.eq_of_toNat_eq; omega
  · omega

private theorem int_umin_comm {w : Nat} (x y : Data.LLVM.Int w) : x.umin y = y.umin x := by
  cases x <;> cases y <;> simp only [Data.LLVM.Int.umin, Id.run]
  rename_i a b
  by_cases h₁ : a.ule b <;> by_cases h₂ : b.ule a <;>
    simp only [h₁, h₂, ↓reduceIte, Bool.false_eq_true] <;>
    simp only [BitVec.ule, decide_eq_true_eq, Bool.not_eq_true, decide_eq_false_iff_not] at h₁ h₂
  · congr 1; apply BitVec.eq_of_toNat_eq; omega
  · omega

private theorem int_and_comm {w : Nat} (x y : Data.LLVM.Int w) : x.and y = y.and x := by
  cases x <;> cases y <;> simp [Data.LLVM.Int.and, BitVec.and_comm, Id.run]

private theorem int_or_comm {w : Nat} (x y : Data.LLVM.Int w) (disjoint : Bool) :
    x.or y disjoint = y.or x disjoint := by
  cases x <;> cases y <;> simp [Data.LLVM.Int.or, BitVec.and_comm, BitVec.or_comm, Id.run]

private theorem int_xor_comm {w : Nat} (x y : Data.LLVM.Int w) : x.xor y = y.xor x := by
  cases x <;> cases y <;> simp [Data.LLVM.Int.xor, BitVec.xor_comm, Id.run]

private theorem int_mul_comm {w : Nat} (x y : Data.LLVM.Int w) (nsw nuw : Bool) :
    x.mul y nsw nuw = y.mul x nsw nuw := by
  cases x <;> cases y <;> simp [Data.LLVM.Int.mul, BitVec.mul_comm, BitVec.smulOverflow,
    BitVec.umulOverflow, Int.mul_comm, Nat.mul_comm, Id.run]

theorem interpretOp'_add_ite (properties : propertiesOf (OpCode.llvm .add))
    (resultTypes : Array TypeAttr) (c : Prop) [Decidable c] (a b : RuntimeValue)
    (blockOperands : Array BlockPtr) (memory : MemoryState) :
    Veir.CTree.interpretOp' (.llvm .add) properties resultTypes
        #[if c then b else a, if c then a else b] blockOperands memory =
      Veir.CTree.interpretOp' (.llvm .add) properties resultTypes #[a, b] blockOperands memory := by
  split
  · simp only [Veir.CTree.interpretOp', Llvm.interpretOpCTree, Llvm.interpretOp']
    cases a <;> cases b <;> simp
    rename_i w x w' y
    by_cases h : w' = w
    · subst h; simp [int_add_comm]
    · simp [h, Ne.symm h]
  · rfl

theorem interpretOp'_intr__smax_ite (properties : propertiesOf (OpCode.llvm .intr__smax))
    (resultTypes : Array TypeAttr) (c : Prop) [Decidable c] (a b : RuntimeValue)
    (blockOperands : Array BlockPtr) (memory : MemoryState) :
    Veir.CTree.interpretOp' (.llvm .intr__smax) properties resultTypes
        #[if c then b else a, if c then a else b] blockOperands memory =
      Veir.CTree.interpretOp' (.llvm .intr__smax) properties resultTypes #[a, b] blockOperands memory := by
  split
  · simp only [Veir.CTree.interpretOp', Llvm.interpretOpCTree, Llvm.interpretOp']
    cases a <;> cases b <;> simp
    rename_i w x w' y
    by_cases h : w' = w
    · subst h; simp [int_smax_comm]
    · simp [h, Ne.symm h]
  · rfl

theorem interpretOp'_intr__smin_ite (properties : propertiesOf (OpCode.llvm .intr__smin))
    (resultTypes : Array TypeAttr) (c : Prop) [Decidable c] (a b : RuntimeValue)
    (blockOperands : Array BlockPtr) (memory : MemoryState) :
    Veir.CTree.interpretOp' (.llvm .intr__smin) properties resultTypes
        #[if c then b else a, if c then a else b] blockOperands memory =
      Veir.CTree.interpretOp' (.llvm .intr__smin) properties resultTypes #[a, b] blockOperands memory := by
  split
  · simp only [Veir.CTree.interpretOp', Llvm.interpretOpCTree, Llvm.interpretOp']
    cases a <;> cases b <;> simp
    rename_i w x w' y
    by_cases h : w' = w
    · subst h; simp [int_smin_comm]
    · simp [h, Ne.symm h]
  · rfl

theorem interpretOp'_intr__umax_ite (properties : propertiesOf (OpCode.llvm .intr__umax))
    (resultTypes : Array TypeAttr) (c : Prop) [Decidable c] (a b : RuntimeValue)
    (blockOperands : Array BlockPtr) (memory : MemoryState) :
    Veir.CTree.interpretOp' (.llvm .intr__umax) properties resultTypes
        #[if c then b else a, if c then a else b] blockOperands memory =
      Veir.CTree.interpretOp' (.llvm .intr__umax) properties resultTypes #[a, b] blockOperands memory := by
  split
  · simp only [Veir.CTree.interpretOp', Llvm.interpretOpCTree, Llvm.interpretOp']
    cases a <;> cases b <;> simp
    rename_i w x w' y
    by_cases h : w' = w
    · subst h; simp [int_umax_comm]
    · simp [h, Ne.symm h]
  · rfl

theorem interpretOp'_intr__umin_ite (properties : propertiesOf (OpCode.llvm .intr__umin))
    (resultTypes : Array TypeAttr) (c : Prop) [Decidable c] (a b : RuntimeValue)
    (blockOperands : Array BlockPtr) (memory : MemoryState) :
    Veir.CTree.interpretOp' (.llvm .intr__umin) properties resultTypes
        #[if c then b else a, if c then a else b] blockOperands memory =
      Veir.CTree.interpretOp' (.llvm .intr__umin) properties resultTypes #[a, b] blockOperands memory := by
  split
  · simp only [Veir.CTree.interpretOp', Llvm.interpretOpCTree, Llvm.interpretOp']
    cases a <;> cases b <;> simp
    rename_i w x w' y
    by_cases h : w' = w
    · subst h; simp [int_umin_comm]
    · simp [h, Ne.symm h]
  · rfl

theorem interpretOp'_and_ite (properties : propertiesOf (OpCode.llvm .and))
    (resultTypes : Array TypeAttr) (c : Prop) [Decidable c] (a b : RuntimeValue)
    (blockOperands : Array BlockPtr) (memory : MemoryState) :
    Veir.CTree.interpretOp' (.llvm .and) properties resultTypes
        #[if c then b else a, if c then a else b] blockOperands memory =
      Veir.CTree.interpretOp' (.llvm .and) properties resultTypes #[a, b] blockOperands memory := by
  split
  · simp only [Veir.CTree.interpretOp', Llvm.interpretOpCTree, Llvm.interpretOp']
    cases a <;> cases b <;> simp
    rename_i w x w' y
    by_cases h : w' = w
    · subst h; simp [int_and_comm]
    · simp [h, Ne.symm h]
  · rfl

theorem interpretOp'_or_ite (properties : propertiesOf (OpCode.llvm .or))
    (resultTypes : Array TypeAttr) (c : Prop) [Decidable c] (a b : RuntimeValue)
    (blockOperands : Array BlockPtr) (memory : MemoryState) :
    Veir.CTree.interpretOp' (.llvm .or) properties resultTypes
        #[if c then b else a, if c then a else b] blockOperands memory =
      Veir.CTree.interpretOp' (.llvm .or) properties resultTypes #[a, b] blockOperands memory := by
  split
  · simp only [Veir.CTree.interpretOp', Llvm.interpretOpCTree, Llvm.interpretOp']
    cases a <;> cases b <;> simp
    rename_i w x w' y
    by_cases h : w' = w
    · subst h; simp [int_or_comm]
    · simp [h, Ne.symm h]
  · rfl

theorem interpretOp'_xor_ite (properties : propertiesOf (OpCode.llvm .xor))
    (resultTypes : Array TypeAttr) (c : Prop) [Decidable c] (a b : RuntimeValue)
    (blockOperands : Array BlockPtr) (memory : MemoryState) :
    Veir.CTree.interpretOp' (.llvm .xor) properties resultTypes
        #[if c then b else a, if c then a else b] blockOperands memory =
      Veir.CTree.interpretOp' (.llvm .xor) properties resultTypes #[a, b] blockOperands memory := by
  split
  · simp only [Veir.CTree.interpretOp', Llvm.interpretOpCTree, Llvm.interpretOp']
    cases a <;> cases b <;> simp
    rename_i w x w' y
    by_cases h : w' = w
    · subst h; simp [int_xor_comm]
    · simp [h, Ne.symm h]
  · rfl

theorem interpretOp'_mul_ite (properties : propertiesOf (OpCode.llvm .mul))
    (resultTypes : Array TypeAttr) (c : Prop) [Decidable c] (a b : RuntimeValue)
    (blockOperands : Array BlockPtr) (memory : MemoryState) :
    Veir.CTree.interpretOp' (.llvm .mul) properties resultTypes
        #[if c then b else a, if c then a else b] blockOperands memory =
      Veir.CTree.interpretOp' (.llvm .mul) properties resultTypes #[a, b] blockOperands memory := by
  split
  · simp only [Veir.CTree.interpretOp', Llvm.interpretOpCTree, Llvm.interpretOp']
    cases a <;> cases b <;> simp
    rename_i w x w' y
    by_cases h : w' = w
    · subst h; simp [int_mul_comm]
    · simp [h, Ne.symm h]
  · rfl

theorem canInterpretTo_add_ite (properties : propertiesOf (OpCode.llvm .add))
    (resultTypes : Array TypeAttr) (c : Prop) [Decidable c] (a b : RuntimeValue)
    (results : Interp (Array RuntimeValue)) :
    CTree.CanInterpretTo (.llvm .add) properties resultTypes
        #[if c then b else a, if c then a else b] results =
      CTree.CanInterpretTo (.llvm .add) properties resultTypes #[a, b] results := by
  simp only [CTree.CanInterpretTo, interpretOp'_add_ite]

theorem canInterpretTo_mul_ite (properties : propertiesOf (OpCode.llvm .mul))
    (resultTypes : Array TypeAttr) (c : Prop) [Decidable c] (a b : RuntimeValue)
    (results : Interp (Array RuntimeValue)) :
    CTree.CanInterpretTo (.llvm .mul) properties resultTypes
        #[if c then b else a, if c then a else b] results =
      CTree.CanInterpretTo (.llvm .mul) properties resultTypes #[a, b] results := by
  simp only [CTree.CanInterpretTo, interpretOp'_mul_ite]

theorem canInterpretTo_intr__smax_ite (properties : propertiesOf (OpCode.llvm .intr__smax))
    (resultTypes : Array TypeAttr) (c : Prop) [Decidable c] (a b : RuntimeValue)
    (results : Interp (Array RuntimeValue)) :
    CTree.CanInterpretTo (.llvm .intr__smax) properties resultTypes
        #[if c then b else a, if c then a else b] results =
      CTree.CanInterpretTo (.llvm .intr__smax) properties resultTypes #[a, b] results := by
  simp only [CTree.CanInterpretTo, interpretOp'_intr__smax_ite]

theorem canInterpretTo_intr__smin_ite (properties : propertiesOf (OpCode.llvm .intr__smin))
    (resultTypes : Array TypeAttr) (c : Prop) [Decidable c] (a b : RuntimeValue)
    (results : Interp (Array RuntimeValue)) :
    CTree.CanInterpretTo (.llvm .intr__smin) properties resultTypes
        #[if c then b else a, if c then a else b] results =
      CTree.CanInterpretTo (.llvm .intr__smin) properties resultTypes #[a, b] results := by
  simp only [CTree.CanInterpretTo, interpretOp'_intr__smin_ite]

theorem canInterpretTo_intr__umax_ite (properties : propertiesOf (OpCode.llvm .intr__umax))
    (resultTypes : Array TypeAttr) (c : Prop) [Decidable c] (a b : RuntimeValue)
    (results : Interp (Array RuntimeValue)) :
    CTree.CanInterpretTo (.llvm .intr__umax) properties resultTypes
        #[if c then b else a, if c then a else b] results =
      CTree.CanInterpretTo (.llvm .intr__umax) properties resultTypes #[a, b] results := by
  simp only [CTree.CanInterpretTo, interpretOp'_intr__umax_ite]

theorem canInterpretTo_intr__umin_ite (properties : propertiesOf (OpCode.llvm .intr__umin))
    (resultTypes : Array TypeAttr) (c : Prop) [Decidable c] (a b : RuntimeValue)
    (results : Interp (Array RuntimeValue)) :
    CTree.CanInterpretTo (.llvm .intr__umin) properties resultTypes
        #[if c then b else a, if c then a else b] results =
      CTree.CanInterpretTo (.llvm .intr__umin) properties resultTypes #[a, b] results := by
  simp only [CTree.CanInterpretTo, interpretOp'_intr__umin_ite]

theorem canInterpretTo_and_ite (properties : propertiesOf (OpCode.llvm .and))
    (resultTypes : Array TypeAttr) (c : Prop) [Decidable c] (a b : RuntimeValue)
    (results : Interp (Array RuntimeValue)) :
    CTree.CanInterpretTo (.llvm .and) properties resultTypes
        #[if c then b else a, if c then a else b] results =
      CTree.CanInterpretTo (.llvm .and) properties resultTypes #[a, b] results := by
  simp only [CTree.CanInterpretTo, interpretOp'_and_ite]

theorem canInterpretTo_or_ite (properties : propertiesOf (OpCode.llvm .or))
    (resultTypes : Array TypeAttr) (c : Prop) [Decidable c] (a b : RuntimeValue)
    (results : Interp (Array RuntimeValue)) :
    CTree.CanInterpretTo (.llvm .or) properties resultTypes
        #[if c then b else a, if c then a else b] results =
      CTree.CanInterpretTo (.llvm .or) properties resultTypes #[a, b] results := by
  simp only [CTree.CanInterpretTo, interpretOp'_or_ite]

theorem canInterpretTo_xor_ite (properties : propertiesOf (OpCode.llvm .xor))
    (resultTypes : Array TypeAttr) (c : Prop) [Decidable c] (a b : RuntimeValue)
    (results : Interp (Array RuntimeValue)) :
    CTree.CanInterpretTo (.llvm .xor) properties resultTypes
        #[if c then b else a, if c then a else b] results =
      CTree.CanInterpretTo (.llvm .xor) properties resultTypes #[a, b] results := by
  simp only [CTree.CanInterpretTo, interpretOp'_xor_ite]

/-- Undo symbolic operand orientations of commutative operations. -/
macro "rewriteCommutedOperands" : tactic => `(tactic|
  simp -failIfUnchanged only [interpretOp'_add_ite, canInterpretTo_add_ite, interpretOp'_mul_ite, canInterpretTo_mul_ite, interpretOp'_intr__smax_ite, canInterpretTo_intr__smax_ite, interpretOp'_intr__smin_ite, canInterpretTo_intr__smin_ite, interpretOp'_intr__umax_ite, canInterpretTo_intr__umax_ite, interpretOp'_intr__umin_ite, canInterpretTo_intr__umin_ite, interpretOp'_and_ite, canInterpretTo_and_ite, interpretOp'_or_ite, canInterpretTo_or_ite, interpretOp'_xor_ite, canInterpretTo_xor_ite])

/-- Normalize a rule, keeping any commutative orientations selected by `swaps` bits symbolic. -/
macro "normalizeInstructionSimplify" : tactic => `(tactic| (
  generalizeSwapBits
  simpPuddleValid
  rewriteCommutedOperands
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
  generalizeSwapBits
  simpPuddleValid
  rewriteCommutedOperands
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
