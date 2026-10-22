import Veir.InstSimplify.ArithmeticSupport
import Init.Data.BitVec.Bitblast

open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify

theorem icmp_iff {rs : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .icmp : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .icmp) props #[IntegerType.mk 1 rs] #[.int w x, .int w y] #[v] ↔
      v = .int 1 (LLVM.Int.icmp x y props.predicate) := by
  simp [InterpretsTo, interpretOp', Llvm.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms, IntegerType.signless]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem select_iff {s : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .select : OpCode))
    (c : LLVM.Int 1) (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .select) props #[IntegerType.mk w s] #[.int 1 c, .int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.select c x y) := by
  simp [InterpretsTo, interpretOp', Llvm.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms, IntegerType.signless]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem int_refines_refl (w : Nat) (x : LLVM.Int w) :
    RuntimeValue.int w x ⊒ .int w x := by
  cases x <;> simp [RuntimeValue.isRefinedBy, isRefinedBy]

theorem int_poison_refines (w : Nat) (x : LLVM.Int w) :
    RuntimeValue.int w .poison ⊒ .int w x := by
  simp [RuntimeValue.isRefinedBy, isRefinedBy]

theorem matched_constant_iff (ty : IntegerType)
    (props : propertiesOf (.llvm .mlir__constant : OpCode)) (n : Int)
    (h : (match props.value with | .integer a => a.value == n | _ => false) = true)
    (v : RuntimeValue) :
    InterpretsTo (.llvm .mlir__constant) props #[ty] #[] #[v] ↔
      v = .int ty.bitwidth (.val (BitVec.ofInt ty.bitwidth n)) := by
  cases hv : props.value <;> simp only [hv, Bool.false_eq_true] at h
  case integer a =>
    have ha : a.value = n := by simpa using h
    simpa [ha] using constant_iff ty props a hv v

/-- Every modeled scalar boolean is poison, false, or true. -/
theorem int1_cases (x : LLVM.Int 1) :
    x = .poison ∨ x = .val 0 ∨ x = .val 1 := by
  cases x with
  | poison => simp
  | val v =>
    have hv : v.toNat < 2 := by simpa using v.isLt
    have hn : v.toNat = 0 ∨ v.toNat = 1 := by omega
    rcases hn with h | h
    · exact Or.inr (Or.inl (congrArg LLVM.Int.val (BitVec.eq_of_toNat_eq (by simpa using h))))
    · exact Or.inr (Or.inr (congrArg LLVM.Int.val (BitVec.eq_of_toNat_eq (by simpa using h))))

theorem smax_iff {s : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .intr__smax : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .intr__smax) props #[IntegerType.mk w s] #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.smax x y) := by
  simp [InterpretsTo, interpretOp', Llvm.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem smin_iff {s : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .intr__smin : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .intr__smin) props #[IntegerType.mk w s] #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.smin x y) := by
  simp [InterpretsTo, interpretOp', Llvm.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem umax_iff {s : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .intr__umax : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .intr__umax) props #[IntegerType.mk w s] #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.umax x y) := by
  simp [InterpretsTo, interpretOp', Llvm.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem umin_iff {s : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .intr__umin : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .intr__umin) props #[IntegerType.mk w s] #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.umin x y) := by
  simp [InterpretsTo, interpretOp', Llvm.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

inductive MinMaxKind where
  | smax | smin | umax | umin
  deriving DecidableEq, Inhabited

def MinMaxKind.op : MinMaxKind → Llvm
  | .smax => .intr__smax
  | .smin => .intr__smin
  | .umax => .intr__umax
  | .umin => .intr__umin

def MinMaxKind.eval (kind : MinMaxKind) {w : Nat} (x y : LLVM.Int w) : LLVM.Int w :=
  match kind with
  | .smax => LLVM.Int.smax x y
  | .smin => LLVM.Int.smin x y
  | .umax => LLVM.Int.umax x y
  | .umin => LLVM.Int.umin x y

def MinMaxKind.strictPred : MinMaxKind → LLVM.IntPred
  | .smax => .sgt
  | .smin => .slt
  | .umax => .ugt
  | .umin => .ult

def MinMaxKind.nonStrictPred : MinMaxKind → LLVM.IntPred
  | .smax => .sge
  | .smin => .sle
  | .umax => .uge
  | .umin => .ule

def MinMaxKind.inverseStrictPred : MinMaxKind → LLVM.IntPred
  | .smax => .slt
  | .smin => .sgt
  | .umax => .ult
  | .umin => .ugt

def MinMaxKind.inverseNonStrictPred : MinMaxKind → LLVM.IntPred
  | .smax => .sle
  | .smin => .sge
  | .umax => .ule
  | .umin => .uge

theorem minmax_iff {s : IntegerType.Signedness} (kind : MinMaxKind) (w : Nat)
    (props : propertiesOf (.llvm kind.op : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm kind.op) props #[IntegerType.mk w s] #[.int w x, .int w y] #[v] ↔
      v = .int w (kind.eval x y) := by
  cases kind
  · exact smax_iff _ _ _ _ _
  · exact smin_iff _ _ _ _ _
  · exact umax_iff _ _ _ _ _
  · exact umin_iff _ _ _ _ _

def swapCmpPred : LLVM.IntPred → LLVM.IntPred
  | .eq => .eq | .ne => .ne
  | .ugt => .ult | .uge => .ule | .ult => .ugt | .ule => .uge
  | .sgt => .slt | .sge => .sle | .slt => .sgt | .sle => .sge

def invertCmpPred : LLVM.IntPred → LLVM.IntPred
  | .eq => .ne | .ne => .eq
  | .ugt => .ule | .uge => .ult | .ult => .uge | .ule => .ugt
  | .sgt => .sle | .sge => .slt | .slt => .sge | .sle => .sgt

def canonicalCmpPred (p : LLVM.IntPred) (swap inverse : Bool) : LLVM.IntPred :=
  let p := match inverse with | true => invertCmpPred p | false => p
  match swap with | true => swapCmpPred p | false => p

theorem clear_mask_eq {w : Nat} (x c : BitVec w)
    (h : x &&& ~~~c = 0) : x &&& c = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  have hi := congrArg (fun v : BitVec w => v.getLsbD i) h
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_zero] at hi ⊢
  cases hx : x.getLsbD i <;> cases hc : c.getLsbD i <;> simp_all

theorem set_mask_eq {w : Nat} (x : BitVec w) (bit : Nat)
    (h : x &&& BitVec.twoPow w bit ≠ 0) : x ||| BitVec.twoPow w bit = x := by
  have hb : x.getLsbD bit = true := by
    cases hv : x.getLsbD bit <;> simp_all [BitVec.and_twoPow]
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_twoPow]
  by_cases hi : bit = i
  · subst i; simp [hb]
  · simp [hi]

theorem odd_sub_ne_self {w : Nat} (x c : BitVec w) (hc : c.getLsbD 0 = true) : c - x ≠ x := by
  intro h
  have he : c = x + x := by
    calc c = (c - x) + x := (BitVec.sub_add_cancel c x).symm
         _ = x + x := by rw [h]
  cases w with
  | zero => simp at hc
  | succ w =>
    have hh := congrArg (fun v : BitVec (w+1) => v.getLsbD 0) he
    simp only [BitVec.getLsbD_add (i := 0) (w := w+1) (by omega) x x, BitVec.carry_zero, Bool.xor_false,
      Bool.xor_self, hc] at hh
    contradiction

theorem subset_toNat_le {w : Nat} (a b : BitVec w) (h : a &&& b = a) : a.toNat ≤ b.toNat := by
  have hn := congrArg BitVec.toNat h
  simp only [BitVec.toNat_and] at hn
  have hl : a.toNat &&& b.toNat ≤ b.toNat := Nat.and_le_right
  omega

theorem and_mask_subset {w : Nat} (x a b : BitVec w) (h : a &&& b = a) :
    (x &&& a) &&& (x &&& b) = x &&& a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  have hi := congrArg (fun v : BitVec w => v.getLsbD i) h
  simp only [BitVec.getLsbD_and] at hi ⊢
  cases hx : x.getLsbD i <;> cases ha : a.getLsbD i <;>
    cases hb : b.getLsbD i <;> simp_all

theorem or_mask_subset {w : Nat} (x a b : BitVec w) (h : a &&& b = a) :
    (x ||| a) &&& (x ||| b) = x ||| a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  have hi := congrArg (fun v : BitVec w => v.getLsbD i) h
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] at hi ⊢
  cases hx : x.getLsbD i <;> cases ha : a.getLsbD i <;>
    cases hb : b.getLsbD i <;> simp_all

def minmaxKind (signed isMin : Bool) : MinMaxKind :=
  match signed, isMin with
  | true, true => .smin | true, false => .smax
  | false, true => .umin | false, false => .umax

@[simp] theorem boolBit_eq_true (b : Bool) : BitVec.ofBool b = 1#1 ↔ b = true := by
  cases b <;> decide

@[simp] theorem boolBit_eq_false (b : Bool) : BitVec.ofBool b = 0#1 ↔ b = false := by
  cases b <;> decide

def icmpEmptyGuard (pred : LLVM.IntPred) (w : Nat) (n : Int) : Bool :=
  let c := BitVec.ofInt w n
  match pred with
  | .ult => c == 0#w | .ugt => c == BitVec.allOnes w
  | .slt => c == BitVec.intMin w | .sgt => c == BitVec.intMax w
  | _ => false

def icmpFullGuard (pred : LLVM.IntPred) (w : Nat) (n : Int) : Bool :=
  let c := BitVec.ofInt w n
  match pred with
  | .uge => c == 0#w | .ule => c == BitVec.allOnes w
  | .sge => c == BitVec.intMin w | .sle => c == BitVec.intMax w
  | _ => false

inductive ScalarLiteral where
  | integer (n : Int)
  | zero
  | poison
  deriving DecidableEq, Inhabited

def ScalarLiteral.eval (lit : ScalarLiteral) (w : Nat) : LLVM.Int w :=
  match lit with
  | .integer n => .val (BitVec.ofInt w n)
  | .zero => .val 0#w
  | .poison => .poison

def matchScalarLiteral (ty : Handle OpCode .type) (lit : ScalarLiteral) :
    MatchProg.Builder (Handle OpCode .value) :=
  match lit with
  | .integer n => matchIntConstant ty n
  | .zero => matchZero ty
  | .poison => matchPoison ty

def createScalarLiteral (ty : Handle OpCode .type) (lit : ScalarLiteral)
    (constantType : IntegerType := IntegerType.signless 1) :
    CreateProg.Builder CreatedOpHandle := do
  match lit with
  | .integer n =>
    let p ← CreateProg.property (.llvm .mlir__constant)
      (LLVMConstantProperties.mk (.integer (IntegerAttr.mk n constantType)))
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p
  | .zero =>
    let p ← CreateProg.property (.llvm .mlir__zero) ()
    CreateProg.operation (.llvm .mlir__zero) #[] #[ty] p
  | .poison =>
    let p ← CreateProg.property (.llvm .mlir__poison) ()
    CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p

def foldCmpLiteral (p : LLVM.IntPred) (w : Nat) (a b : ScalarLiteral) : ScalarLiteral :=
  match a, b with
  | .poison, _ | _, .poison => .poison
  | .integer a, .integer b => .integer (if p.eval (BitVec.ofInt w a) (BitVec.ofInt w b) then 1 else 0)
  | .zero, .integer b => .integer (if p.eval 0#w (BitVec.ofInt w b) then 1 else 0)
  | .integer a, .zero => .integer (if p.eval (BitVec.ofInt w a) 0#w then 1 else 0)
  | .zero, .zero => .integer (if p.eval 0#w 0#w then 1 else 0)

theorem bool_bit_integer (b : Bool) :
    BitVec.ofBool b = BitVec.ofInt 1 (if b then 1 else 0) := by
  cases b <;> rfl

theorem fold_cmp_literal_refines (p : LLVM.IntPred) (w : Nat) (a b : ScalarLiteral) :
    RuntimeValue.int 1 (LLVM.Int.icmp (a.eval w) (b.eval w) p) ⊒
      .int 1 ((foldCmpLiteral p w a b).eval 1) := by
  cases a <;> cases b <;>
    simp [foldCmpLiteral, ScalarLiteral.eval, LLVM.Int.icmp, Id.run, pure,
      RuntimeValue.isRefinedBy, isRefinedBy, bool_bit_integer]

def foldSelectLiteral (cond trueVal falseVal : ScalarLiteral) : ScalarLiteral :=
  match cond with
  | .poison => .poison
  | .zero => falseVal
  | .integer n => if BitVec.ofInt 1 n == 1#1 then trueVal else falseVal

@[simp] theorem bv_ule_self {w : Nat} (x : BitVec w) : x.ule x = true := by
  simp [BitVec.ule]
@[simp] theorem bv_ult_self {w : Nat} (x : BitVec w) : x.ult x = false := by
  simp [BitVec.ult]
@[simp] theorem bv_zero_ule {w : Nat} (x : BitVec w) : (0#w).ule x = true := by
  simp [BitVec.ule]
@[simp] theorem bv_ult_zero {w : Nat} (x : BitVec w) : x.ult 0#w = false := by
  simp [BitVec.ult]
@[simp] theorem bv_ule_allOnes {w : Nat} (x : BitVec w) : x.ule (BitVec.allOnes w) = true := by
  have hn := x.isLt
  simp only [BitVec.ule, BitVec.toNat_allOnes, decide_eq_true_eq]
  omega
@[simp] theorem bv_allOnes_ult {w : Nat} (x : BitVec w) : (BitVec.allOnes w).ult x = false := by
  have hn := x.isLt
  simp only [BitVec.ult, BitVec.toNat_allOnes, decide_eq_false_iff_not]
  omega

theorem cmp_urem_mul_self {w : Nat} (x m : BitVec w) (h : ¬ x.umulOverflow m) :
    (x*m)%m = 0#w := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_umod, BitVec.toNat_mul_of_not_umulOverflow h, Nat.mul_mod]

theorem cmp_srem_mul_self {w : Nat} (x m : BitVec w) (h : ¬ x.smulOverflow m) :
    (x*m).srem m = 0#w := by
  apply BitVec.srem_zero_of_dvd
  rw [BitVec.toInt_mul_of_not_smulOverflow h]
  exact Int.dvd_mul_left _ _

end Veir.InstSimplify
