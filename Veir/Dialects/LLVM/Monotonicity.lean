module

import all Veir.Dialects.LLVM.OpInfo
import all Veir.Interpreter.Basic
import all Veir.Data.Refinement
public import Veir.Interpreter.Lemmas
public import Veir.Data.LLVM.Byte.Lemmas

public section

/-!
# Monotonicity of the LLVM interpreter

An LLVM opcode is monotone in its operands when refining its operands refines its result. Every
opcode proved monotone here has its own `InterpretOp'Monotone` instance; an opcode without one
falls back to the assumption in `Veir.Dialects.Monotonicity`. One instance covers both refinement
modes. In assembly mode a pointer may be refined by the wild pointer at its address, and the
memory opcodes hold up because the two resolve to the same object wherever the source accesses
memory.

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
theorem Llvm.intBinaryArm_mono {operands operands' : Array RuntimeValue} {mem : MemoryState}
    {asm : Bool} (hwf : RefinementMode.Wf asm mem) {width : Nat → Nat} (f : {bw : Nat} → Int bw → Int bw → Int (width bw))
    (hf : ∀ {bw : Nat} {x x' y y' : Int bw}, x ⊒ x' → y ⊒ y' → f x y ⊒ f x' y')
    (h : operands ⊒[.of asm mem] operands') :
    Interp.isRefinedBy (OperationResult.isRefinedByFrom mem asm)
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
    · exact OperationResult.isRefinedByFrom_value hwf
        (RuntimeValue.int_isRefinedBy (hf hl (Int.cast_mono _ _ _ hr)))
  case _ => simp [Interp.isRefinedBy]

/-- The arm of a division, which is undefined behaviour on some operands. -/
theorem Llvm.intDivisionArm_mono {operands operands' : Array RuntimeValue} {mem : MemoryState}
    {asm : Bool} (hwf : RefinementMode.Wf asm mem) (f : {bw : Nat} → Int bw → Int bw → Int bw) (ub : {bw : Nat} → Int bw → Int bw → Bool)
    (hf : ∀ {bw : Nat} {x x' y y' : Int bw}, x ⊒ x' → y ⊒ y' → f x y ⊒ f x' y')
    (hub : ∀ {bw : Nat} {x x' y y' : Int bw}, x ⊒ x' → y ⊒ y' → ub x y = false → ub x' y' = false)
    (h : operands ⊒[.of asm mem] operands') :
    Interp.isRefinedBy (OperationResult.isRefinedByFrom mem asm)
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
        exact OperationResult.isRefinedByFrom_value hwf
          (RuntimeValue.int_isRefinedBy (hf hl (Int.cast_mono _ _ _ hr)))
  case _ => simp [Interp.isRefinedBy]

/-- The arm of an operation that reads one integer operand. -/
theorem Llvm.intUnaryArm_mono {operands operands' : Array RuntimeValue} {mem : MemoryState}
    {asm : Bool} (hwf : RefinementMode.Wf asm mem) (f : {bw : Nat} → Int bw → Int bw)
    (hf : ∀ {bw : Nat} {x x' : Int bw}, x ⊒ x' → f x ⊒ f x')
    (h : operands ⊒[.of asm mem] operands') :
    Interp.isRefinedBy (OperationResult.isRefinedByFrom mem asm)
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
    exact OperationResult.isRefinedByFrom_value hwf (RuntimeValue.int_isRefinedBy (hf hx))
  case _ => simp [Interp.isRefinedBy]

/-- The arm of an operation that reads three integer operands of the same width. -/
theorem Llvm.intTernaryArm_mono {operands operands' : Array RuntimeValue} {mem : MemoryState}
    {asm : Bool} (hwf : RefinementMode.Wf asm mem) (f : {bw : Nat} → Int bw → Int bw → Int bw → Int bw)
    (hf : ∀ {bw : Nat} {a a' b b' c c' : Int bw},
      a ⊒ a' → b ⊒ b' → c ⊒ c' → f a b c ⊒ f a' b' c')
    (h : operands ⊒[.of asm mem] operands') :
    Interp.isRefinedBy (OperationResult.isRefinedByFrom mem asm)
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
      · exact OperationResult.isRefinedByFrom_value hwf (RuntimeValue.int_isRefinedBy
          (hf ha (Int.cast_mono _ _ _ hb) (Int.cast_mono _ _ _ hc)))
  case _ => simp [Interp.isRefinedBy]

/-- The arm of an operation that widens one integer operand to its result type. -/
theorem Llvm.intExtendArm_mono {operands operands' : Array RuntimeValue}
    (resultTypes : Array TypeAttr) {mem : MemoryState} {asm : Bool}
    (hwf : RefinementMode.Wf asm mem) (f : {w : Nat} → Int w → (w' : Nat) → w < w' → Int w')
    (hf : ∀ {w : Nat} {x x' : Int w} {w' : Nat} (hw : w < w'), x ⊒ x' → f x w' hw ⊒ f x' w' hw)
    (h : operands ⊒[.of asm mem] operands') :
    Interp.isRefinedBy (OperationResult.isRefinedByFrom mem asm)
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
        | exact OperationResult.isRefinedByFrom_value hwf (RuntimeValue.int_isRefinedBy (hf _ hv))
        | simp [Interp.isRefinedBy]
    case _ => simp [Interp.isRefinedBy]
  case _ => simp [Interp.isRefinedBy]

/-! ## Operations that do not read their operands -/

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .mlir__constant) where
  monotone _ _ _ _ _ mem hwf _ := by
    simp only [interpretOp', Llvm.interpretOp']
    repeat' split
    all_goals first
      | exact Interp.isRefinedBy_fail_target
      | exact OperationResult.isRefinedByFrom_value hwf (RuntimeValue.isRefinedBy_refl_of fun _ =>
          trivial)

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .mlir__poison) where
  monotone _ _ _ _ _ mem hwf _ := by
    simp only [interpretOp', Llvm.interpretOp']
    repeat' split
    all_goals first
      | exact Interp.isRefinedBy_fail_target
      | exact OperationResult.isRefinedByFrom_value hwf (RuntimeValue.isRefinedBy_refl_of fun _ =>
          trivial)

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .mlir__zero) where
  monotone _ _ _ _ _ mem hwf _ := by
    simp only [interpretOp', Llvm.interpretOp']
    repeat' split
    all_goals first
      | exact Interp.isRefinedBy_fail_target
      | exact OperationResult.isRefinedByFrom_value hwf (RuntimeValue.isRefinedBy_refl_of fun ha =>
          RuntimeValue.validIn_null (hwf ha))
      | exact OperationResult.isRefinedByFrom_value hwf (RuntimeValue.isRefinedBy_refl_of fun _ =>
          trivial)

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .mlir__addressof) where
  monotone _ _ _ _ _ mem hwf _ := by
    simp only [interpretOp', Llvm.interpretOp']
    repeat' split
    all_goals first
      | exact Interp.isRefinedBy_fail_target
      | exact OperationResult.isRefinedByFrom_value hwf (RuntimeValue.isRefinedBy_refl_of fun _ =>
          ⟨by assumption, by simp⟩)

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .unreachable) where
  monotone _ _ _ _ _ _ _ _ := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Interp.isRefinedBy_ub_target

/-! ## Integer arithmetic -/

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .add) where
  monotone props _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intBinaryArm_mono hwf (fun l r => LLVM.Int.add l r props.nsw props.nuw)
      (fun hl hr => Int.add_mono _ _ _ _ hl hr _ _) h

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .sub) where
  monotone props _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intBinaryArm_mono hwf (fun l r => LLVM.Int.sub l r props.nsw props.nuw)
      (fun hl hr => Int.sub_mono _ _ _ _ hl hr _ _) h

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .mul) where
  monotone props _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intBinaryArm_mono hwf (fun l r => LLVM.Int.mul l r props.nsw props.nuw)
      (fun hl hr => Int.mul_mono _ _ _ _ hl hr _ _) h

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .udiv) where
  monotone props _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intDivisionArm_mono hwf (fun l r => LLVM.Int.udiv l r props.exact)
      (fun _ r => LLVM.Int.isUnsignedDivisionUB r)
      (fun hl hr => Int.udiv_mono _ _ _ _ hl hr _)
      (fun _ hr hub => Int.isUnsignedDivisionUB_eq_false_mono hr hub) h

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .sdiv) where
  monotone props _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intDivisionArm_mono hwf (fun l r => LLVM.Int.sdiv l r props.exact)
      (fun l r => LLVM.Int.isSignedDivisionUB l r)
      (fun hl hr => Int.sdiv_mono _ _ _ _ hl hr _)
      (fun hl hr hub => Int.isSignedDivisionUB_eq_false_mono hl hr hub) h

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .urem) where
  monotone _ _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intDivisionArm_mono hwf (fun l r => LLVM.Int.urem l r)
      (fun _ r => LLVM.Int.isUnsignedDivisionUB r)
      (fun hl hr => Int.urem_mono _ _ _ _ hl hr)
      (fun _ hr hub => Int.isUnsignedDivisionUB_eq_false_mono hr hub) h

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .srem) where
  monotone _ _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intDivisionArm_mono hwf (fun l r => LLVM.Int.srem l r)
      (fun l r => LLVM.Int.isSignedDivisionUB l r)
      (fun hl hr => Int.srem_mono _ _ _ _ hl hr)
      (fun hl hr hub => Int.isSignedDivisionUB_eq_false_mono hl hr hub) h

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .ashr) where
  monotone props _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intBinaryArm_mono hwf (fun l r => LLVM.Int.ashr l r props.exact)
      (fun hl hr => Int.ashr_mono _ _ _ _ hl hr _) h

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .and) where
  monotone _ _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intBinaryArm_mono hwf (fun l r => LLVM.Int.and l r)
      (fun hl hr => Int.and_mono _ _ _ _ hl hr) h

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .or) where
  monotone props _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intBinaryArm_mono hwf (fun l r => LLVM.Int.or l r props.disjoint)
      (fun hl hr => Int.or_mono _ _ _ _ _ hl hr) h

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .xor) where
  monotone _ _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intBinaryArm_mono hwf (fun l r => LLVM.Int.xor l r)
      (fun hl hr => Int.xor_mono _ _ _ _ hl hr) h

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .icmp) where
  monotone props _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intBinaryArm_mono hwf (fun l r => LLVM.Int.icmp l r props.predicate)
      (fun hl hr => Int.icmp_mono _ _ _ _ _ hl hr) h

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .intr__smax) where
  monotone _ _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intBinaryArm_mono hwf (fun l r => LLVM.Int.smax l r)
      (fun hl hr => Int.smax_mono _ _ _ _ hl hr) h

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .intr__smin) where
  monotone _ _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intBinaryArm_mono hwf (fun l r => LLVM.Int.smin l r)
      (fun hl hr => Int.smin_mono _ _ _ _ hl hr) h

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .intr__umax) where
  monotone _ _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intBinaryArm_mono hwf (fun l r => LLVM.Int.umax l r)
      (fun hl hr => Int.umax_mono _ _ _ _ hl hr) h

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .intr__umin) where
  monotone _ _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intBinaryArm_mono hwf (fun l r => LLVM.Int.umin l r)
      (fun hl hr => Int.umin_mono _ _ _ _ hl hr) h

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .intr__sadd__sat) where
  monotone _ _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intBinaryArm_mono hwf (fun l r => LLVM.Int.saddSat l r)
      (fun hl hr => Int.saddSat_mono _ _ _ _ hl hr) h

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .intr__uadd__sat) where
  monotone _ _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intBinaryArm_mono hwf (fun l r => LLVM.Int.uaddSat l r)
      (fun hl hr => Int.uaddSat_mono _ _ _ _ hl hr) h

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .intr__ssub__sat) where
  monotone _ _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intBinaryArm_mono hwf (fun l r => LLVM.Int.ssubSat l r)
      (fun hl hr => Int.ssubSat_mono _ _ _ _ hl hr) h

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .intr__usub__sat) where
  monotone _ _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intBinaryArm_mono hwf (fun l r => LLVM.Int.usubSat l r)
      (fun hl hr => Int.usubSat_mono _ _ _ _ hl hr) h

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .intr__sshl__sat) where
  monotone _ _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intBinaryArm_mono hwf (fun l r => LLVM.Int.sshlSat l r)
      (fun hl hr => Int.sshlSat_mono _ _ _ _ hl hr) h

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .intr__ushl__sat) where
  monotone _ _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intBinaryArm_mono hwf (fun l r => LLVM.Int.ushlSat l r)
      (fun hl hr => Int.ushlSat_mono _ _ _ _ hl hr) h

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .intr__fshl) where
  monotone _ _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intTernaryArm_mono hwf (fun a b c => LLVM.Int.fshl a b c)
      (fun ha hb hc => Int.fshl_mono _ _ _ _ _ _ ha hb hc) h

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .intr__fshr) where
  monotone _ _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intTernaryArm_mono hwf (fun a b c => LLVM.Int.fshr a b c)
      (fun ha hb hc => Int.fshr_mono _ _ _ _ _ _ ha hb hc) h

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .intr__ctlz) where
  monotone props _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intUnaryArm_mono hwf (fun x => LLVM.Int.ctlz x props.is_zero_poison)
      (fun hx => Int.ctlz_mono _ _ _ hx) h

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .intr__cttz) where
  monotone props _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intUnaryArm_mono hwf (fun x => LLVM.Int.cttz x props.is_zero_poison)
      (fun hx => Int.cttz_mono _ _ _ hx) h

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .intr__ctpop) where
  monotone _ _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intUnaryArm_mono hwf (fun x => LLVM.Int.ctpop x)
      (fun hx => Int.ctpop_mono _ _ hx) h

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .intr__bswap) where
  monotone _ _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intUnaryArm_mono hwf (fun x => LLVM.Int.bswap x)
      (fun hx => Int.bswap_mono _ _ hx) h

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .intr__bitreverse) where
  monotone _ _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intUnaryArm_mono hwf (fun x => LLVM.Int.bitreverse x)
      (fun hx => Int.bitreverse_mono _ _ hx) h

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .intr__abs) where
  monotone props _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intUnaryArm_mono hwf (fun x => LLVM.Int.abs x props.is_int_min_poison)
      (fun hx => Int.abs_mono _ _ _ hx) h

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .select) where
  monotone _ _ _ _ _ mem hwf h := by
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
      · exact OperationResult.isRefinedByFrom_value hwf (RuntimeValue.int_isRefinedBy
          (Int.select_mono _ _ _ _ _ _ hl (Int.cast_mono _ _ _ hr) hc))
    case _ => simp [Interp.isRefinedBy]

/-! ## Casts -/

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .zext) where
  monotone props resultTypes _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intExtendArm_mono resultTypes hwf
      (fun v w' hw => LLVM.Int.zext v w' props.nneg hw) (fun hw hv => Int.zext_mono _ _ hw hv) h

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .sext) where
  monotone _ resultTypes _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact Llvm.intExtendArm_mono resultTypes hwf
      (fun v w' hw => LLVM.Int.sext v w' hw) (fun hw hv => Int.sext_mono _ _ hw hv) h

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .trunc) where
  monotone _ _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    case _ val hOps =>
      obtain ⟨w₁, hw, h₁⟩ := RuntimeValue.arrayIsRefinedBy_toList_singleton hOps h
      cases val
      case int bw v =>
        obtain ⟨v', rfl, hv⟩ := RuntimeValue.int_of_isRefinedBy h₁
        simp only [hw]
        split
        case _ resType hres =>
          obtain ⟨attr, hattr⟩ := resType
          cases attr <;> try exact Interp.isRefinedBy_fail_target
          case integerType ty =>
            by_cases hle : ty.bitwidth ≥ bw
            · simp [hle, Interp.isRefinedBy]
            · simp only [hle, ↓reduceDIte]
              exact OperationResult.isRefinedByFrom_value hwf (RuntimeValue.int_isRefinedBy
                (Int.trunc_mono _ _ _ hv))
        case _ => simp [Interp.isRefinedBy]
      case byte bw v =>
        obtain ⟨v', rfl, hv⟩ := RuntimeValue.byte_of_isRefinedBy h₁
        simp only [hw]
        split
        case _ resType hres =>
          obtain ⟨attr, hattr⟩ := resType
          cases attr <;> try exact Interp.isRefinedBy_fail_target
          case byteType ty =>
            by_cases hle : ty.bitwidth ≥ bw
            · simp [hle, Interp.isRefinedBy]
            · simp only [hle, ↓reduceDIte]
              exact OperationResult.isRefinedByFrom_value hwf (RuntimeValue.byte_isRefinedBy
                (Data.LLVM.Byte.trunc_mono hv))
        case _ => simp [Interp.isRefinedBy]
      all_goals (split <;> simp [Interp.isRefinedBy])
    case _ => simp [Interp.isRefinedBy]

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .bitcast) where
  monotone _ _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    case _ val hOps =>
      obtain ⟨w₁, hw, h₁⟩ := RuntimeValue.arrayIsRefinedBy_toList_singleton hOps h
      cases val
      case int bw v =>
        obtain ⟨v', rfl, hv⟩ := RuntimeValue.int_of_isRefinedBy h₁
        simp only [hw]
        split
        · rename_i attr property hres
          clear hres
          cases attr
          case integerType ty =>
            cases ty
            dsimp only
            split
            · exact Interp.isRefinedBy_fail_target
            · exact OperationResult.isRefinedByFrom_value hwf (RuntimeValue.int_isRefinedBy hv)
          case byteType ty =>
            cases ty
            dsimp only
            split
            · exact Interp.isRefinedBy_fail_target
            · exact OperationResult.isRefinedByFrom_value hwf (RuntimeValue.byte_isRefinedBy
                (Data.LLVM.Byte.fromInt_mono hv))
          all_goals exact Interp.isRefinedBy_fail_target
        · simp [Interp.isRefinedBy]
      case byte bw v =>
        obtain ⟨v', rfl, hv⟩ := RuntimeValue.byte_of_isRefinedBy h₁
        simp only [hw]
        split
        · rename_i attr property hres
          clear hres
          cases attr
          case byteType ty =>
            cases ty
            dsimp only
            split
            · exact Interp.isRefinedBy_fail_target
            · exact OperationResult.isRefinedByFrom_value hwf (RuntimeValue.byte_isRefinedBy hv)
          case integerType ty =>
            cases ty
            dsimp only
            split
            · exact Interp.isRefinedBy_fail_target
            · exact OperationResult.isRefinedByFrom_value hwf (RuntimeValue.int_isRefinedBy
                (Data.LLVM.Byte.toInt_mono hv))
          case llvmPointerType ty =>
            dsimp only
            split
            next heq =>
              subst heq
              simp only [Data.LLVM.Byte.cast_self]
              exact OperationResult.isRefinedByFrom_value hwf
                (MemoryState.ptrFromInt_isRefinedBy_of hwf (Data.LLVM.Byte.toInt_mono hv))
            next => exact Interp.isRefinedBy_fail_target
          all_goals exact Interp.isRefinedBy_fail_target
        · simp [Interp.isRefinedBy]
      case addr p =>
        obtain ⟨q, rfl⟩ := RuntimeValue.exists_addr_of_isRefinedBy h₁
        simp only [hw]
        split
        · rename_i attr property hres
          clear hres
          cases attr
          case byteType ty =>
            cases ty
            dsimp only
            split
            · exact OperationResult.isRefinedByFrom_value hwf (RuntimeValue.byte_isRefinedBy
                (Data.LLVM.Byte.fromInt_mono (MemoryState.intFromPtr_isRefinedBy_of hwf h₁)))
            · exact Interp.isRefinedBy_fail_target
          case llvmPointerType ty =>
            exact OperationResult.isRefinedByFrom_value hwf h₁
          all_goals exact Interp.isRefinedBy_fail_target
        · simp [Interp.isRefinedBy]
      all_goals (split <;> simp [Interp.isRefinedBy])
    case _ => simp [Interp.isRefinedBy]

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .inttoptr) where
  monotone _ _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    case _ bw v hOps =>
      obtain ⟨w₁, hw, h₁⟩ := RuntimeValue.arrayIsRefinedBy_toList_singleton hOps h
      obtain ⟨v', rfl, hv⟩ := RuntimeValue.int_of_isRefinedBy h₁
      simp only [hw]
      split
      case _ type hres =>
        obtain ⟨attr, hattr⟩ := type
        cases attr <;> try exact Interp.isRefinedBy_fail_target
        dsimp only
        split
        · exact OperationResult.isRefinedByFrom_value hwf
            (MemoryState.ptrFromInt_isRefinedBy_of hwf (Int.cast_mono _ _ _ hv))
        · exact Interp.isRefinedBy_fail_target
      case _ => simp [Interp.isRefinedBy]
    case _ => simp [Interp.isRefinedBy]

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .ptrtoint) where
  monotone _ _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    case _ p hOps =>
      obtain ⟨w₁, hw, h₁⟩ := RuntimeValue.arrayIsRefinedBy_toList_singleton hOps h
      obtain ⟨q, rfl⟩ := RuntimeValue.exists_addr_of_isRefinedBy h₁
      simp only [hw]
      split
      case _ type hres =>
        obtain ⟨attr, hattr⟩ := type
        cases attr <;> try exact Interp.isRefinedBy_fail_target
        rename_i ty
        cases ty
        dsimp only
        split
        · exact OperationResult.isRefinedByFrom_value hwf (RuntimeValue.int_isRefinedBy
            (MemoryState.intFromPtr_isRefinedBy_of hwf h₁))
        · exact Interp.isRefinedBy_fail_target
      case _ => simp [Interp.isRefinedBy]
    case _ => simp [Interp.isRefinedBy]

/-! ## Control flow -/

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .return) where
  monotone _ _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    exact ⟨⟨⟨rfl, fun i hi => by simp at hi⟩, rfl,
      by simpa [ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy] using h, hwf⟩,
      fun _ => MemoryState.Extends.refl mem⟩

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .br) where
  monotone _ _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    case _ dest hDest =>
      exact ⟨⟨⟨rfl, fun i hi => by simp at hi⟩, rfl,
        by simp [ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy, h], hwf⟩,
        fun _ => MemoryState.Extends.refl mem⟩
    case _ => simp [Interp.isRefinedBy]

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .cond_br) where
  monotone _ _ _ _ _ mem hwf h := by
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
                exact ⟨⟨⟨rfl, fun i hi => by simp at hi⟩, rfl,
                  by simp [ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy,
                    RuntimeValue.arrayIsRefinedBy_extract h], hwf⟩,
                  fun _ => MemoryState.Extends.refl mem⟩
              · simp only [hcond, ↓reduceIte]
                exact ⟨⟨⟨rfl, fun i hi => by simp at hi⟩, rfl,
                  by simp [ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy,
                    RuntimeValue.arrayIsRefinedBy_extract_from h], hwf⟩,
                  fun _ => MemoryState.Extends.refl mem⟩
            | 1, .poison => simp [Interp.isRefinedBy]
            | 0, _ | (_ + 2), _ => simp [Interp.isRefinedBy]
          all_goals simp [Interp.isRefinedBy]
        case _ => simp [Interp.isRefinedBy]
      case _ => simp [Interp.isRefinedBy]
    case _ => simp [Interp.isRefinedBy]

/-! ## Memory -/

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .alloca) where
  monotone _ _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    case _ bw count hOps =>
      obtain ⟨w₁, hw, h₁⟩ := RuntimeValue.arrayIsRefinedBy_toList_singleton hOps h
      obtain rfl := RuntimeValue.int_val_of_isRefinedBy h₁
      simp only [hw]
      refine Interp.isRefinedBy_refl_of_ok fun r hr => ?_
      simp only [Interp.bind_eq_ok_iff] at hr
      obtain ⟨_, -, _, -, ⟨mem', addr⟩, halloc, hr⟩ := hr
      simp only [Interp.pure_eq, Interp.ok.injEq] at hr
      subst hr
      exact OperationResult.isRefinedByFrom_alloc hwf halloc
    case _ => simp [Interp.isRefinedBy]

/-- A load through a refined pointer reads what the source read. -/
instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .load) where
  monotone _ _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · split
      · next ptr hOps =>
        obtain ⟨w, hw, hRef⟩ := RuntimeValue.arrayIsRefinedBy_toList_singleton hOps h
        obtain ⟨q, rfl, -, -⟩ := RuntimeValue.addr_val_of_isRefinedBy_of hRef
        rw [hw]
        dsimp only
        split
        · exact Interp.isRefinedBy_bind (MemoryState.llvmLoad_isRefinedBy_of hwf hRef _)
            (fun _ _ hv => OperationResult.isRefinedByFrom_value hwf hv)
        · simp [Interp.isRefinedBy]
      · simp [Interp.isRefinedBy]
    · simp [Interp.isRefinedBy]

instance (asm : Bool) : InterpretOp'Monotone asm (.llvm .getelementptr) where
  monotone _ _ _ _ _ mem hwf h := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    case _ ptr bw idx hOps =>
      obtain ⟨w₁, w₂, hw, h₁, h₂⟩ := RuntimeValue.arrayIsRefinedBy_toList_pair hOps h
      obtain ⟨idx', rfl, hi⟩ := RuntimeValue.int_of_isRefinedBy h₂
      obtain ⟨p', rfl⟩ := RuntimeValue.exists_addr_of_isRefinedBy h₁
      simp only [hw]
      refine Interp.isRefinedBy_bind_same _ (fun size => ?_)
      cases ptr
      case poison =>
        cases p' <;> cases idx' <;>
          exact OperationResult.isRefinedByFrom_value hwf RuntimeValue.addr_poison_isRefinedBy
      case val p =>
        obtain ⟨q, hq, -, -⟩ := RuntimeValue.addr_val_of_isRefinedBy_of h₁
        cases hq
        cases idx
        case poison =>
          cases idx' <;>
            exact OperationResult.isRefinedByFrom_value hwf RuntimeValue.addr_poison_isRefinedBy
        case val v =>
          obtain rfl : idx' = .val v := by cases idx' <;> simp_all [isRefinedBy]
          exact OperationResult.isRefinedByFrom_value hwf
            (RuntimeValue.addr_addOffset_isRefinedBy h₁ _)
    case _ => simp [Interp.isRefinedBy]

end Veir

end
