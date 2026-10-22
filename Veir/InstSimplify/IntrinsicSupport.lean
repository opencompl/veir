import Veir.InstSimplify.CmpSelectSupport
import Veir.InstSimplify.LogicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify

theorem bswap_iff {s : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .intr__bswap : OpCode))
    (x : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .intr__bswap) props #[IntegerType.mk w s] #[.int w x] #[v] ↔
      v = .int w (LLVM.Int.bswap x) := by
  simp [InterpretsTo, interpretOp', Llvm.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem bitreverse_iff {s : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .intr__bitreverse : OpCode))
    (x : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .intr__bitreverse) props #[IntegerType.mk w s] #[.int w x] #[v] ↔
      v = .int w (LLVM.Int.bitreverse x) := by
  simp [InterpretsTo, interpretOp', Llvm.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem ctpop_iff {s : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .intr__ctpop : OpCode))
    (x : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .intr__ctpop) props #[IntegerType.mk w s] #[.int w x] #[v] ↔
      v = .int w (LLVM.Int.ctpop x) := by
  simp [InterpretsTo, interpretOp', Llvm.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem ctlz_iff {s : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .intr__ctlz : OpCode))
    (x : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .intr__ctlz) props #[IntegerType.mk w s] #[.int w x] #[v] ↔
      v = .int w (LLVM.Int.ctlz x props.is_zero_poison) := by
  simp [InterpretsTo, interpretOp', Llvm.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem cttz_iff {s : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .intr__cttz : OpCode))
    (x : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .intr__cttz) props #[IntegerType.mk w s] #[.int w x] #[v] ↔
      v = .int w (LLVM.Int.cttz x props.is_zero_poison) := by
  simp [InterpretsTo, interpretOp', Llvm.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem abs_iff {s : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .intr__abs : OpCode))
    (x : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .intr__abs) props #[IntegerType.mk w s] #[.int w x] #[v] ↔
      v = .int w (LLVM.Int.abs x props.is_int_min_poison) := by
  simp [InterpretsTo, interpretOp', Llvm.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem saddSat_iff {s : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .intr__sadd__sat : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .intr__sadd__sat) props #[IntegerType.mk w s] #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.saddSat x y) := by
  simp [InterpretsTo, interpretOp', Llvm.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem uaddSat_iff {s : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .intr__uadd__sat : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .intr__uadd__sat) props #[IntegerType.mk w s] #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.uaddSat x y) := by
  simp [InterpretsTo, interpretOp', Llvm.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem ssubSat_iff {s : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .intr__ssub__sat : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .intr__ssub__sat) props #[IntegerType.mk w s] #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.ssubSat x y) := by
  simp [InterpretsTo, interpretOp', Llvm.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem usubSat_iff {s : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .intr__usub__sat : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .intr__usub__sat) props #[IntegerType.mk w s] #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.usubSat x y) := by
  simp [InterpretsTo, interpretOp', Llvm.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem fshl_iff {s : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .intr__fshl : OpCode))
    (x y z : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .intr__fshl) props #[IntegerType.mk w s] #[.int w x, .int w y, .int w z] #[v] ↔
      v = .int w (LLVM.Int.fshl x y z) := by
  simp [InterpretsTo, interpretOp', Llvm.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem fshr_iff {s : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .intr__fshr : OpCode))
    (x y z : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .intr__fshr) props #[IntegerType.mk w s] #[.int w x, .int w y, .int w z] #[v] ↔
      v = .int w (LLVM.Int.fshr x y z) := by
  simp [InterpretsTo, interpretOp', Llvm.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

def MinMaxKind.saturation (kind : MinMaxKind) (w : Nat) : BitVec w :=
  match kind with
  | .smax => BitVec.intMax w
  | .smin => BitVec.intMin w
  | .umax => BitVec.allOnes w
  | .umin => 0

def MinMaxKind.inverse (kind : MinMaxKind) : MinMaxKind :=
  match kind with
  | .smax => .smin | .smin => .smax | .umax => .umin | .umin => .umax

def matchMinMaxLimit (ty : Handle OpCode .type) (kind : MinMaxKind) : MatchProg.Builder (Handle OpCode .value) := do
  let c ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
  MatchProg.matchNative (ty,c.properties) (fun (ty,p) => match ty.val,p.value with
    | .integerType t, .integer a => BitVec.ofInt t.bitwidth a.value == kind.saturation t.bitwidth
    | _,_ => false)
  return c.res[0]!

def minMaxLimitGuard (ty : TypeAttr) (p : propertiesOf (.llvm .mlir__constant : OpCode)) (kind : MinMaxKind) : Bool :=
  match ty.val,p.value with
  | .integerType t, .integer a => BitVec.ofInt t.bitwidth a.value == kind.saturation t.bitwidth
  | _,_ => false

theorem matched_minmax_limit_eq (ty : IntegerType) (p : propertiesOf (.llvm .mlir__constant : OpCode))
    (kind : MinMaxKind) (v : RuntimeValue) (hi : InterpretsTo (.llvm .mlir__constant) p #[ty] #[] #[v])
    (hc : minMaxLimitGuard ty p kind = true) :
    v = .int ty.bitwidth (.val (kind.saturation ty.bitwidth)) := by
  cases hp : p.value with
  | integer a =>
    have hc : BitVec.ofInt ty.bitwidth a.value = kind.saturation ty.bitwidth := by
      simpa [minMaxLimitGuard, TypeAttr.of_val, Attribute.of, -Attribute.integerType_eq_of, hp] using hc
    simpa [hc] using (constant_iff ty p a hp v).mp hi
  | _ => simp [minMaxLimitGuard, TypeAttr.of_val, Attribute.of, -Attribute.integerType_eq_of, hp] at hc

theorem abs_bits_idem {w : Nat} (x : BitVec w) :
    (if (if x.msb then -x else x).msb then -(if x.msb then -x else x) else (if x.msb then -x else x)) = (if x.msb then -x else x) := by
  by_cases hm : x.msb = true
  · simp only [hm, ↓reduceIte]
    by_cases hmin : x = BitVec.intMin w
    · subst x
      simp [BitVec.neg_intMin]
    · have hx := BitVec.toInt_neg_of_msb_true hm
      have hn := BitVec.toInt_neg_of_ne_intMin hmin
      have hs : (-x).msb = false := by
        have hnonneg : 0 ≤ (-x).toInt := by omega
        simp [BitVec.msb_eq_toInt, Int.not_lt.mpr hnonneg]
      simp [hs]
  · have hm : x.msb = false := Bool.eq_false_iff.mpr hm
    simp [hm]

theorem funnel_left_zero_shift {w : Nat} (a b : BitVec w) :
    ((a ++ b) <<< 0).extractLsb' w w = a := by
  simp [BitVec.extractLsb'_append_eq_left]
theorem funnel_right_zero_shift {w : Nat} (a b : BitVec w) :
    ((a ++ b) >>> 0).truncate w = b := by
  simp [BitVec.truncate, BitVec.setWidth_append_eq_right]

theorem funnel_left_ones {w : Nat} (c : BitVec w) :
    (((BitVec.allOnes w ++ BitVec.allOnes w) <<< (c.toNat % w)).extractLsb' w w) = BitVec.allOnes w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  by_cases hi : i < w
  · have hw : 0 < w := by omega
    have hs := Nat.mod_lt c.toNat hw
    simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append,
      BitVec.getLsbD_allOnes, hi, show c.toNat % w ≤ w+i by omega,
      show w+i-c.toNat%w < w+w by omega]
    simp only [BitVec.getElem_append, BitVec.getElem_allOnes]
    split <;> rfl
  · simp [BitVec.getLsbD_of_ge, Nat.le_of_not_gt hi]
theorem funnel_right_ones {w : Nat} (c : BitVec w) :
    (((BitVec.allOnes w ++ BitVec.allOnes w) >>> (c.toNat % w)).truncate w) = BitVec.allOnes w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  by_cases hi : i < w
  · have hw : 0 < w := by omega
    have hs := Nat.mod_lt c.toNat hw
    simp [BitVec.truncate, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append,
      BitVec.getLsbD_allOnes, hi, show i+c.toNat%w < w+w by omega]
    omega
  · simp [BitVec.getLsbD_of_ge, Nat.le_of_not_gt hi]

theorem sshlSat_iff {s : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .intr__sshl__sat : OpCode)) (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .intr__sshl__sat) props #[IntegerType.mk w s] #[.int w x,.int w y] #[v] ↔
      v = .int w (LLVM.Int.sshlSat x y) := by
  simp [InterpretsTo, interpretOp', Llvm.interpretOp', RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩; exact (h .empty).symm
  · grind

theorem ushlSat_iff {s : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .intr__ushl__sat : OpCode)) (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .intr__ushl__sat) props #[IntegerType.mk w s] #[.int w x,.int w y] #[v] ↔
      v = .int w (LLVM.Int.ushlSat x y) := by
  simp [InterpretsTo, interpretOp', Llvm.interpretOp', RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩; exact (h .empty).symm
  · grind

theorem intrinsic_constant_success (ty : IntegerType) (p : propertiesOf (.llvm .mlir__constant : OpCode))
    (v : RuntimeValue) (h : InterpretsTo (.llvm .mlir__constant) p #[ty] #[] #[v]) :
    ∃ a : IntegerAttr, p.value = .integer a ∧
      v = .int ty.bitwidth (.val (BitVec.ofInt ty.bitwidth a.value)) := by
  cases ty
  cases hp : p.value with
  | integer a => exact ⟨a, rfl, (constant_iff _ p a hp v).mp h⟩
  | float a | dense a | string a =>
    simp [InterpretsTo, interpretOp', Llvm.interpretOp', hp, TypeAttr.of_val,
      Attribute.of, -Attribute.integerType_eq_of] at h
    exact False.elim (h.2 MemoryState.empty)

def intrinsic_result_bits {w : Nat} : LLVM.Int w → BitVec w
  | .poison => 0
  | .val r => r
theorem ctz_one_shift {w : Nat} (s : BitVec w) (hs : s.toNat < w) :
    (1#w <<< s).ctz = s := by
  have hw : 0 < w := by omega
  have hbit : ∀ i, (1#w <<< s).getLsbD i = decide (i = s.toNat) := by
    intro i
    by_cases hi : i = s.toNat
    · subst i
      simp [BitVec.shiftLeft_eq', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one, hw, hs]
    · simp [BitVec.shiftLeft_eq', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one, hi]
      omega
  have hn : (1#w <<< s) ≠ 0#w := by
    intro hz
    have h := hbit s.toNat
    simp [hz] at h
  have ht := BitVec.getLsbD_true_ctz_of_ne_zero hn
  rw [hbit] at ht
  have he : (1#w <<< s).ctz.toNat = s.toNat := of_decide_eq_true ht
  exact BitVec.eq_of_toNat_eq he

theorem ctlz_negative_bits {w : Nat} (x : BitVec w) (hx : x.msb = true) : x.clz = 0#w := by
  have hw : 0 < w := by
    by_cases h : w = 0
    · subst w
      have he : x = 0#0 := Subsingleton.elim _ _
      simp [he] at hx
    · omega
  apply BitVec.eq_of_toNat_eq
  simpa using (BitVec.clz_eq_zero_iff hw).mpr (BitVec.le_toNat_of_msb_true hx)

theorem ctlz_negative {w : Nat} (x : BitVec w) (hx : x.msb = true) (zp : Bool) :
    LLVM.Int.ctlz (.val x) zp = .val 0 := by
  have hn : x ≠ 0#w := by intro he; simp [he] at hx
  simp only [LLVM.Int.ctlz, Id.run, pure]
  rw [if_neg (by intro h; exact hn h.2)]
  exact congrArg LLVM.Int.val (ctlz_negative_bits x hx)
theorem clz_negative_lshr {w : Nat} (a s : BitVec w) (ha : a.msb = true) (hs : s.toNat < w) :
    (a >>> s).clz = s := by
  have hw : 0 < w := by omega
  let y := a >>> s
  have hbit : y.getLsbD (w-1-s.toNat) = true := by
    dsimp only [y]
    simp only [BitVec.ushiftRight_eq', BitVec.getLsbD_ushiftRight]
    rw [show s.toNat + (w-1-s.toNat) = w-1 by omega]
    simpa only [← BitVec.msb_eq_getLsbD_last] using ha
  have hn : y ≠ 0#w := by intro hz; simp [hz] at hbit
  have hc : y.clz.toNat ≤ w := by
    have hh := BitVec.clz_le (x := y)
    change y.clz.toNat ≤ (BitVec.ofNat w w).toNat at hh
    simpa only [BitVec.toNat_ofNat, Nat.mod_two_pow_self] using hh
  have hf : ∀ j, y.getLsbD (w-y.clz.toNat+j) = false := by
    apply BitVec.getLsbD_false_of_clzAuxRec
    intro i hi
    simp [show w ≤ i by omega]
  have hlow : s.toNat ≤ y.clz.toNat := by
    have ht := BitVec.getLsbD_true_clz_of_ne_zero hw hn
    by_cases hl : s.toNat ≤ y.clz.toNat
    · exact hl
    · have hi : w ≤ s.toNat + (w-1-y.clz.toNat) := by omega
      dsimp only [y] at ht
      simp only [BitVec.ushiftRight_eq', BitVec.getLsbD_ushiftRight] at ht
      have hi' : w ≤ s.toNat + (w-1-(a >>> s.toNat).clz.toNat) := hi
      rw [BitVec.getLsbD_of_ge a _ hi'] at ht
      contradiction
  have hhigh : y.clz.toNat ≤ s.toNat := by
    by_cases hh : y.clz.toNat ≤ s.toNat
    · exact hh
    · have hhf := hf (y.clz.toNat-1-s.toNat)
      rw [show w-y.clz.toNat+(y.clz.toNat-1-s.toNat) = w-1-s.toNat by omega] at hhf
      rw [hbit] at hhf
      contradiction
  apply BitVec.eq_of_toNat_eq
  dsimp only [y] at hlow hhigh
  omega
theorem funnel_left_decompose {w : Nat} (a b : BitVec w) (s : Nat) (hs : s < w) :
    ((a ++ b) <<< s).extractLsb' w w = (a <<< s) ||| (b >>> (w-s)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  by_cases hi : i < w
  · simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append,
      BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight]
    by_cases his : i < s
    · simp [hi, his, show s ≤ w+i by omega, show w+i-s < w by omega,
        show ¬s ≤ i by omega, show w-s+i = w+i-s by omega]
    · simp [hi, his, show s ≤ w+i by omega, show ¬w+i-s < w by omega,
        show s ≤ i by omega, show w ≤ w-s+i by omega,
        show w+i-s-w = i-s by omega]
  · simp [BitVec.getLsbD_of_ge, Nat.le_of_not_gt hi]

theorem funnel_right_decompose {w : Nat} (a b : BitVec w) (s : Nat) (hs : s < w) :
    ((a ++ b) >>> s).truncate w = (a <<< (w-s)) ||| (b >>> s) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  by_cases hi : i < w
  · simp only [BitVec.truncate, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append,
      BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight]
    by_cases his : i < w-s
    · simp [hi, his, show s+i < w by omega, show ¬w-s ≤ i by omega]
    · simp [hi, his, show ¬s+i < w by omega, show w-s ≤ i by omega,
        show s+i-w = i-(w-s) by omega]
      intro hb
      rw [BitVec.getLsbD_of_ge b _ (by omega)] at hb
      contradiction
  · simp [BitVec.getLsbD_of_ge, Nat.le_of_not_gt hi]

end Veir.InstSimplify
