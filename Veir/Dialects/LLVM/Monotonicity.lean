module

import all Veir.Dialects.LLVM.OpInfo
import all Veir.Interpreter.Basic
public import Veir.Interpreter.Lemmas

public section

/-!
# Monotonicity of the LLVM interpreter

An LLVM opcode is monotone in its operands when refining its operands refines its result. Every
opcode proved monotone here has its own `InterpretOp'Monotone` instance; an opcode without one
falls back to the assumption in `Veir.Dialects.Monotonicity`. This file proves the integer
operations and the control flow. The casts and the memory operations, which also reason about
bytes and pointers, follow separately. Of the opcodes the interpreter implements, these are not
monotone in the relation as it stands:

* `freeze` turns poison into zero, so a more defined operand gives a *different* result;
* `store`, `memset`, `memcpy` and `memmove` write a poison byte where a refined operand writes a
  concrete one, which the relation rejects because it asks for the two memories to be equal rather
  than refined;
* `shl` and `lshr` read a byte, and refinement of bytes is bit by bit, which needs shift lemmas
  that `Veir.Data.LLVM.Byte` does not have yet;
* `switch` picks its successor inside a loop, so relating the two runs needs an induction over
  that loop.

The arms of the integer operations share a few shapes. Each shape has one lemma, generic in the
operation, and the instance of an opcode applies it to the operation's own monotonicity lemma.
-/

open Veir.Data
open Veir.Data.LLVM

namespace Veir

/-! ## The shapes of the integer arms -/

/--
The arm of an operation that reads two integer operands of the same width. The result's width
is a function of theirs: the same for arithmetic, one for a comparison.
-/
theorem Llvm.intBinaryArm_mono {operands operands' : Array RuntimeValue} (mem : MemoryState)
    {width : Nat → Nat} (f : {bw : Nat} → Int bw → Int bw → Int (width bw))
    (hf : ∀ {bw : Nat} {x x' y y' : Int bw}, x ⊒ x' → y ⊒ y' → f x y ⊒ f x' y')
    (h : operands ⊒ operands') :
    Interp.isRefinedBy OperationResult.isRefinedBy
      (do let [.int bw lhs, .int bw' rhs] := operands.toList | none
          if h : bw' ≠ bw then none else
          let rhs := rhs.cast (by simp at h; exact h)
          return (#[.int (width bw) (f lhs rhs)], mem, none))
      (do let [.int bw lhs, .int bw' rhs] := operands'.toList | none
          if h : bw' ≠ bw then none else
          let rhs := rhs.cast (by simp at h; exact h)
          return (#[.int (width bw) (f lhs rhs)], mem, none)) := by
  split
  case _ bw lhs bw' rhs hOps =>
    obtain ⟨w₁, w₂, hw, h₁, h₂⟩ := RuntimeValue.arrayIsRefinedBy_toList_pair hOps h
    obtain ⟨lhs', rfl, hl⟩ := RuntimeValue.int_of_isRefinedBy h₁
    obtain ⟨rhs', rfl, hr⟩ := RuntimeValue.int_of_isRefinedBy h₂
    rw [hw]
    dsimp only
    split
    · simp [Interp.isRefinedBy]
    · exact OperationResult.isRefinedBy_value
        (RuntimeValue.int_isRefinedBy (hf hl (Int.cast_mono _ _ _ hr)))
  case _ => simp [Interp.isRefinedBy]

/-- The arm of a division, which is undefined behaviour on some operands. -/
theorem Llvm.intDivisionArm_mono {operands operands' : Array RuntimeValue} (mem : MemoryState)
    (f : {bw : Nat} → Int bw → Int bw → Int bw) (ub : {bw : Nat} → Int bw → Int bw → Bool)
    (hf : ∀ {bw : Nat} {x x' y y' : Int bw}, x ⊒ x' → y ⊒ y' → f x y ⊒ f x' y')
    (hub : ∀ {bw : Nat} {x x' y y' : Int bw}, x ⊒ x' → y ⊒ y' → ub x y = false → ub x' y' = false)
    (h : operands ⊒ operands') :
    Interp.isRefinedBy OperationResult.isRefinedBy
      (do let [.int bw lhs, .int bw' rhs] := operands.toList | none
          if h : bw' ≠ bw then none else
          let rhs := rhs.cast (by simp at h; exact h)
          if ub lhs rhs then Interp.ub none
          return (#[.int bw (f lhs rhs)], mem, none))
      (do let [.int bw lhs, .int bw' rhs] := operands'.toList | none
          if h : bw' ≠ bw then none else
          let rhs := rhs.cast (by simp at h; exact h)
          if ub lhs rhs then Interp.ub none
          return (#[.int bw (f lhs rhs)], mem, none)) := by
  split
  case _ bw lhs bw' rhs hOps =>
    obtain ⟨w₁, w₂, hw, h₁, h₂⟩ := RuntimeValue.arrayIsRefinedBy_toList_pair hOps h
    obtain ⟨lhs', rfl, hl⟩ := RuntimeValue.int_of_isRefinedBy h₁
    obtain ⟨rhs', rfl, hr⟩ := RuntimeValue.int_of_isRefinedBy h₂
    rw [hw]
    dsimp only
    split
    · simp [Interp.isRefinedBy]
    · split
      · simp [Interp.isRefinedBy]
      · next hNot =>
        rw [hub hl (Int.cast_mono _ _ _ hr) (by simpa using hNot)]
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact OperationResult.isRefinedBy_value
          (RuntimeValue.int_isRefinedBy (hf hl (Int.cast_mono _ _ _ hr)))
  case _ => simp [Interp.isRefinedBy]

/-- The arm of an operation that reads one integer operand. -/
theorem Llvm.intUnaryArm_mono {operands operands' : Array RuntimeValue} (mem : MemoryState)
    (f : {bw : Nat} → Int bw → Int bw)
    (hf : ∀ {bw : Nat} {x x' : Int bw}, x ⊒ x' → f x ⊒ f x')
    (h : operands ⊒ operands') :
    Interp.isRefinedBy OperationResult.isRefinedBy
      (do let [.int bw x] := operands.toList | none
          return (#[.int bw (f x)], mem, none))
      (do let [.int bw x] := operands'.toList | none
          return (#[.int bw (f x)], mem, none)) := by
  split
  case _ bw x hOps =>
    obtain ⟨w₁, hw, h₁⟩ := RuntimeValue.arrayIsRefinedBy_toList_singleton hOps h
    obtain ⟨x', rfl, hx⟩ := RuntimeValue.int_of_isRefinedBy h₁
    rw [hw]
    dsimp only
    exact OperationResult.isRefinedBy_value (RuntimeValue.int_isRefinedBy (hf hx))
  case _ => simp [Interp.isRefinedBy]

/-- The arm of an operation that reads three integer operands of the same width. -/
theorem Llvm.intTernaryArm_mono {operands operands' : Array RuntimeValue} (mem : MemoryState)
    (f : {bw : Nat} → Int bw → Int bw → Int bw → Int bw)
    (hf : ∀ {bw : Nat} {a a' b b' c c' : Int bw},
      a ⊒ a' → b ⊒ b' → c ⊒ c' → f a b c ⊒ f a' b' c')
    (h : operands ⊒ operands') :
    Interp.isRefinedBy OperationResult.isRefinedBy
      (do let [.int bw a, .int bw' b, .int bw'' c] := operands.toList | none
          if h : bw' ≠ bw then none else
          if h'' : bw'' ≠ bw then none else
          let b := b.cast (by simp at h; exact h)
          let c := c.cast (by simp at h''; exact h'')
          return (#[.int bw (f a b c)], mem, none))
      (do let [.int bw a, .int bw' b, .int bw'' c] := operands'.toList | none
          if h : bw' ≠ bw then none else
          if h'' : bw'' ≠ bw then none else
          let b := b.cast (by simp at h; exact h)
          let c := c.cast (by simp at h''; exact h'')
          return (#[.int bw (f a b c)], mem, none)) := by
  split
  case _ bw a bw' b bw'' c hOps =>
    obtain ⟨w₁, w₂, w₃, hw, h₁, h₂, h₃⟩ := RuntimeValue.arrayIsRefinedBy_toList_triple hOps h
    obtain ⟨a', rfl, ha⟩ := RuntimeValue.int_of_isRefinedBy h₁
    obtain ⟨b', rfl, hb⟩ := RuntimeValue.int_of_isRefinedBy h₂
    obtain ⟨c', rfl, hc⟩ := RuntimeValue.int_of_isRefinedBy h₃
    rw [hw]
    dsimp only
    split
    · simp [Interp.isRefinedBy]
    · split
      · simp [Interp.isRefinedBy]
      · exact OperationResult.isRefinedBy_value (RuntimeValue.int_isRefinedBy
          (hf ha (Int.cast_mono _ _ _ hb) (Int.cast_mono _ _ _ hc)))
  case _ => simp [Interp.isRefinedBy]

/-- The arm of an operation that widens one integer operand to its result type. -/
theorem Llvm.intExtendArm_mono {operands operands' : Array RuntimeValue}
    (resultTypes : Array TypeAttr) (mem : MemoryState)
    (f : {w : Nat} → Int w → (w' : Nat) → w < w' → Int w')
    (hf : ∀ {w : Nat} {x x' : Int w} {w' : Nat} (hw : w < w'), x ⊒ x' → f x w' hw ⊒ f x' w' hw)
    (h : operands ⊒ operands') :
    Interp.isRefinedBy OperationResult.isRefinedBy
      (do let [.int w val] := operands.toList | none
          let some resType := resultTypes[0]? | none
          let .integerType resBw := resType.val | none
          if h : resBw.bitwidth <= w then none else
          return (#[.int resBw.bitwidth (f val resBw.bitwidth (by omega))], mem, none))
      (do let [.int w val] := operands'.toList | none
          let some resType := resultTypes[0]? | none
          let .integerType resBw := resType.val | none
          if h : resBw.bitwidth <= w then none else
          return (#[.int resBw.bitwidth (f val resBw.bitwidth (by omega))], mem, none)) := by
  split
  case _ w val hOps =>
    obtain ⟨w₁, hw, h₁⟩ := RuntimeValue.arrayIsRefinedBy_toList_singleton hOps h
    obtain ⟨val', rfl, hv⟩ := RuntimeValue.int_of_isRefinedBy h₁
    simp only [hw]
    split
    case _ resType hres =>
      obtain ⟨attr, hattr⟩ := resType
      cases attr <;> try exact Interp.isRefinedBy_fail_target
      split <;> try split
      all_goals first
        | exact OperationResult.isRefinedBy_value (RuntimeValue.int_isRefinedBy (hf _ hv))
        | simp [Interp.isRefinedBy]
    case _ => simp [Interp.isRefinedBy]
  case _ => simp [Interp.isRefinedBy]

/-! ## Operations that do not read their operands -/

instance : InterpretOp'Monotone (.llvm .mlir__constant) where
  monotone _ _ _ _ _ _ _ := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Interp.isRefinedBy_refl_operationResult _

instance : InterpretOp'Monotone (.llvm .mlir__poison) where
  monotone _ _ _ _ _ _ _ := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Interp.isRefinedBy_refl_operationResult _

instance : InterpretOp'Monotone (.llvm .mlir__zero) where
  monotone _ _ _ _ _ _ _ := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Interp.isRefinedBy_refl_operationResult _

instance : InterpretOp'Monotone (.llvm .mlir__addressof) where
  monotone _ _ _ _ _ _ _ := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Interp.isRefinedBy_refl_operationResult _

instance : InterpretOp'Monotone (.llvm .unreachable) where
  monotone _ _ _ _ _ _ _ := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Interp.isRefinedBy_ub_target

/-! ## Integer arithmetic -/

instance : InterpretOp'Monotone (.llvm .add) where
  monotone props _ _ _ _ mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intBinaryArm_mono mem (fun l r => LLVM.Int.add l r props.nsw props.nuw)
      (fun hl hr => Int.add_mono _ _ _ _ hl hr _ _) h

instance : InterpretOp'Monotone (.llvm .sub) where
  monotone props _ _ _ _ mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intBinaryArm_mono mem (fun l r => LLVM.Int.sub l r props.nsw props.nuw)
      (fun hl hr => Int.sub_mono _ _ _ _ hl hr _ _) h

instance : InterpretOp'Monotone (.llvm .mul) where
  monotone props _ _ _ _ mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intBinaryArm_mono mem (fun l r => LLVM.Int.mul l r props.nsw props.nuw)
      (fun hl hr => Int.mul_mono _ _ _ _ hl hr _ _) h

instance : InterpretOp'Monotone (.llvm .udiv) where
  monotone props _ _ _ _ mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intDivisionArm_mono mem (fun l r => LLVM.Int.udiv l r props.exact)
      (fun _ r => LLVM.Int.isUnsignedDivisionUB r)
      (fun hl hr => Int.udiv_mono _ _ _ _ hl hr _)
      (fun _ hr hub => Int.isUnsignedDivisionUB_eq_false_mono hr hub) h

instance : InterpretOp'Monotone (.llvm .sdiv) where
  monotone props _ _ _ _ mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intDivisionArm_mono mem (fun l r => LLVM.Int.sdiv l r props.exact)
      (fun l r => LLVM.Int.isSignedDivisionUB l r)
      (fun hl hr => Int.sdiv_mono _ _ _ _ hl hr _)
      (fun hl hr hub => Int.isSignedDivisionUB_eq_false_mono hl hr hub) h

instance : InterpretOp'Monotone (.llvm .urem) where
  monotone _ _ _ _ _ mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intDivisionArm_mono mem (fun l r => LLVM.Int.urem l r)
      (fun _ r => LLVM.Int.isUnsignedDivisionUB r)
      (fun hl hr => Int.urem_mono _ _ _ _ hl hr)
      (fun _ hr hub => Int.isUnsignedDivisionUB_eq_false_mono hr hub) h

instance : InterpretOp'Monotone (.llvm .srem) where
  monotone _ _ _ _ _ mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intDivisionArm_mono mem (fun l r => LLVM.Int.srem l r)
      (fun l r => LLVM.Int.isSignedDivisionUB l r)
      (fun hl hr => Int.srem_mono _ _ _ _ hl hr)
      (fun hl hr hub => Int.isSignedDivisionUB_eq_false_mono hl hr hub) h

instance : InterpretOp'Monotone (.llvm .ashr) where
  monotone props _ _ _ _ mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intBinaryArm_mono mem (fun l r => LLVM.Int.ashr l r props.exact)
      (fun hl hr => Int.ashr_mono _ _ _ _ hl hr _) h

instance : InterpretOp'Monotone (.llvm .and) where
  monotone _ _ _ _ _ mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intBinaryArm_mono mem (fun l r => LLVM.Int.and l r)
      (fun hl hr => Int.and_mono _ _ _ _ hl hr) h

instance : InterpretOp'Monotone (.llvm .or) where
  monotone props _ _ _ _ mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intBinaryArm_mono mem (fun l r => LLVM.Int.or l r props.disjoint)
      (fun hl hr => Int.or_mono _ _ _ _ _ hl hr) h

instance : InterpretOp'Monotone (.llvm .xor) where
  monotone _ _ _ _ _ mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intBinaryArm_mono mem (fun l r => LLVM.Int.xor l r)
      (fun hl hr => Int.xor_mono _ _ _ _ hl hr) h

instance : InterpretOp'Monotone (.llvm .icmp) where
  monotone props _ _ _ _ mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intBinaryArm_mono mem (fun l r => LLVM.Int.icmp l r props.predicate)
      (fun hl hr => Int.icmp_mono _ _ _ _ _ hl hr) h

instance : InterpretOp'Monotone (.llvm .intr__smax) where
  monotone _ _ _ _ _ mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intBinaryArm_mono mem (fun l r => LLVM.Int.smax l r)
      (fun hl hr => Int.smax_mono _ _ _ _ hl hr) h

instance : InterpretOp'Monotone (.llvm .intr__smin) where
  monotone _ _ _ _ _ mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intBinaryArm_mono mem (fun l r => LLVM.Int.smin l r)
      (fun hl hr => Int.smin_mono _ _ _ _ hl hr) h

instance : InterpretOp'Monotone (.llvm .intr__umax) where
  monotone _ _ _ _ _ mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intBinaryArm_mono mem (fun l r => LLVM.Int.umax l r)
      (fun hl hr => Int.umax_mono _ _ _ _ hl hr) h

instance : InterpretOp'Monotone (.llvm .intr__umin) where
  monotone _ _ _ _ _ mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intBinaryArm_mono mem (fun l r => LLVM.Int.umin l r)
      (fun hl hr => Int.umin_mono _ _ _ _ hl hr) h

instance : InterpretOp'Monotone (.llvm .intr__sadd__sat) where
  monotone _ _ _ _ _ mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intBinaryArm_mono mem (fun l r => LLVM.Int.saddSat l r)
      (fun hl hr => Int.saddSat_mono _ _ _ _ hl hr) h

instance : InterpretOp'Monotone (.llvm .intr__uadd__sat) where
  monotone _ _ _ _ _ mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intBinaryArm_mono mem (fun l r => LLVM.Int.uaddSat l r)
      (fun hl hr => Int.uaddSat_mono _ _ _ _ hl hr) h

instance : InterpretOp'Monotone (.llvm .intr__ssub__sat) where
  monotone _ _ _ _ _ mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intBinaryArm_mono mem (fun l r => LLVM.Int.ssubSat l r)
      (fun hl hr => Int.ssubSat_mono _ _ _ _ hl hr) h

instance : InterpretOp'Monotone (.llvm .intr__usub__sat) where
  monotone _ _ _ _ _ mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intBinaryArm_mono mem (fun l r => LLVM.Int.usubSat l r)
      (fun hl hr => Int.usubSat_mono _ _ _ _ hl hr) h

instance : InterpretOp'Monotone (.llvm .intr__sshl__sat) where
  monotone _ _ _ _ _ mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intBinaryArm_mono mem (fun l r => LLVM.Int.sshlSat l r)
      (fun hl hr => Int.sshlSat_mono _ _ _ _ hl hr) h

instance : InterpretOp'Monotone (.llvm .intr__ushl__sat) where
  monotone _ _ _ _ _ mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intBinaryArm_mono mem (fun l r => LLVM.Int.ushlSat l r)
      (fun hl hr => Int.ushlSat_mono _ _ _ _ hl hr) h

instance : InterpretOp'Monotone (.llvm .intr__fshl) where
  monotone _ _ _ _ _ mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intTernaryArm_mono mem (fun a b c => LLVM.Int.fshl a b c)
      (fun ha hb hc => Int.fshl_mono _ _ _ _ _ _ ha hb hc) h

instance : InterpretOp'Monotone (.llvm .intr__fshr) where
  monotone _ _ _ _ _ mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intTernaryArm_mono mem (fun a b c => LLVM.Int.fshr a b c)
      (fun ha hb hc => Int.fshr_mono _ _ _ _ _ _ ha hb hc) h

instance : InterpretOp'Monotone (.llvm .intr__ctlz) where
  monotone props _ _ _ _ mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intUnaryArm_mono mem (fun x => LLVM.Int.ctlz x props.is_zero_poison)
      (fun hx => Int.ctlz_mono _ _ _ hx) h

instance : InterpretOp'Monotone (.llvm .intr__cttz) where
  monotone props _ _ _ _ mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intUnaryArm_mono mem (fun x => LLVM.Int.cttz x props.is_zero_poison)
      (fun hx => Int.cttz_mono _ _ _ hx) h

instance : InterpretOp'Monotone (.llvm .intr__ctpop) where
  monotone _ _ _ _ _ mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intUnaryArm_mono mem (fun x => LLVM.Int.ctpop x)
      (fun hx => Int.ctpop_mono _ _ hx) h

instance : InterpretOp'Monotone (.llvm .intr__bswap) where
  monotone _ _ _ _ _ mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intUnaryArm_mono mem (fun x => LLVM.Int.bswap x)
      (fun hx => Int.bswap_mono _ _ hx) h

instance : InterpretOp'Monotone (.llvm .intr__bitreverse) where
  monotone _ _ _ _ _ mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intUnaryArm_mono mem (fun x => LLVM.Int.bitreverse x)
      (fun hx => Int.bitreverse_mono _ _ hx) h

instance : InterpretOp'Monotone (.llvm .intr__abs) where
  monotone props _ _ _ _ mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intUnaryArm_mono mem (fun x => LLVM.Int.abs x props.is_int_min_poison)
      (fun hx => Int.abs_mono _ _ _ hx) h

instance : InterpretOp'Monotone (.llvm .select) where
  monotone _ _ _ _ _ _ h := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    case _ cond bw lhs bw' rhs hOps =>
      obtain ⟨w₁, w₂, w₃, hw, h₁, h₂, h₃⟩ := RuntimeValue.arrayIsRefinedBy_toList_triple hOps h
      obtain ⟨cond', rfl, hc⟩ := RuntimeValue.int_of_isRefinedBy h₁
      obtain ⟨lhs', rfl, hl⟩ := RuntimeValue.int_of_isRefinedBy h₂
      obtain ⟨rhs', rfl, hr⟩ := RuntimeValue.int_of_isRefinedBy h₃
      simp only [hw]
      split
      · simp [Interp.isRefinedBy]
      · exact OperationResult.isRefinedBy_value (RuntimeValue.int_isRefinedBy
          (Int.select_mono _ _ _ _ _ _ hl (Int.cast_mono _ _ _ hr) hc))
    case _ => simp [Interp.isRefinedBy]

/-! ## Integer casts -/

instance : InterpretOp'Monotone (.llvm .zext) where
  monotone props resultTypes _ _ _ mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intExtendArm_mono resultTypes mem
      (fun v w' hw => LLVM.Int.zext v w' props.nneg hw) (fun hw hv => Int.zext_mono _ _ hw hv) h

instance : InterpretOp'Monotone (.llvm .sext) where
  monotone _ resultTypes _ _ _ mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intExtendArm_mono resultTypes mem
      (fun v w' hw => LLVM.Int.sext v w' hw) (fun hw hv => Int.sext_mono _ _ hw hv) h

/-! ## Control flow -/

instance : InterpretOp'Monotone (.llvm .return) where
  monotone _ _ _ _ _ _ h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact ⟨⟨rfl, fun i hi => by simp at hi⟩, rfl, h⟩

instance : InterpretOp'Monotone (.llvm .br) where
  monotone _ _ _ _ _ _ h := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    case _ dest hDest =>
      exact ⟨⟨rfl, fun i hi => by simp at hi⟩, rfl, rfl, h⟩
    case _ => simp [Interp.isRefinedBy]

instance : InterpretOp'Monotone (.llvm .cond_br) where
  monotone _ _ _ _ _ _ h := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    case _ destTrue destFalse hDest =>
      split
      case _ condVal hCond =>
        obtain ⟨w, hw, hRef⟩ := RuntimeValue.getElem?_of_arrayIsRefinedBy h hCond
        simp only [hw]
        split
        case _ trueSize hSize =>
          rcases condVal with _ | _ | _ | _ | _ | _
          case int bw v =>
            match bw, v with
            | 1, .val c =>
              obtain rfl := RuntimeValue.int_val_of_isRefinedBy hRef
              by_cases hcond : c = 1#1
              · simp only [hcond, ↓reduceIte]
                exact ⟨⟨rfl, fun i hi => by simp at hi⟩, rfl, rfl,
                  RuntimeValue.arrayIsRefinedBy_extract h _ _⟩
              · simp only [hcond, ↓reduceIte]
                exact ⟨⟨rfl, fun i hi => by simp at hi⟩, rfl, rfl,
                  RuntimeValue.arrayIsRefinedBy_extract_from h _⟩
            | 1, .poison => simp [Interp.isRefinedBy]
            | 0, _ | (_ + 2), _ => simp [Interp.isRefinedBy]
          all_goals simp [Interp.isRefinedBy]
        case _ => simp [Interp.isRefinedBy]
      case _ => simp [Interp.isRefinedBy]
    case _ => simp [Interp.isRefinedBy]

/-! ## Memory -/

/--
A load is monotone: a poison pointer is undefined behavior and
a concrete one is fixed by refinement.
-/
instance : InterpretOp'Monotone (.llvm .load) where
  monotone props resultTypes operands operands' blockOperands mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · split
      · next ptr hOps =>
        obtain ⟨w, hw, hRef⟩ := RuntimeValue.arrayIsRefinedBy_toList_singleton hOps h
        obtain rfl := RuntimeValue.addr_val_of_isRefinedBy hRef
        rw [hw]
        exact Interp.isRefinedBy_refl_operationResult _
      · simp [Interp.isRefinedBy]
    · simp [Interp.isRefinedBy]

end Veir

end
