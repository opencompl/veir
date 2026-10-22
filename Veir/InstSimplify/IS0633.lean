import Veir.InstSimplify.ArithmeticExtra
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS0633
private theorem xor_signmask_add (x : BitVec w) : (x ^^^ BitVec.intMin w) + BitVec.intMin w = x := by
  cases w with
  | zero => simp [BitVec.of_length_zero]
  | succ n =>
    have hm : BitVec.intMin (n+1) = BitVec.cons true (0#n) := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_cons', BitVec.toNat_intMin_of_pos, Nat.shiftLeft_eq]
    rw [hm, ← BitVec.cons_msb_setWidth x]
    generalize x.msb = b
    generalize x.setWidth n = lo
    simp only [BitVec.cons_xor_cons, BitVec.xor_zero]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_cons', Nat.shiftLeft_eq]
    have h := lo.isLt
    cases b <;> simp only [Bool.false_xor, Bool.true_xor, Bool.not_true, Bool.not_false, Bool.toNat_false, Bool.toNat_true, Nat.zero_mul, Nat.one_mul, Nat.zero_add, BitVec.toNat_zero, Nat.add_zero, Nat.pow_succ]
    · have heq : 2 ^ n + lo.toNat + 2 ^ n = lo.toNat + 2 ^ n * 2 := by omega
      rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · rw [Nat.mod_eq_of_lt (by omega)]
      omega
private theorem refines (y : LLVM.Int w) (p : NswNuwProperties) :
    RuntimeValue.int w (LLVM.Int.add (LLVM.Int.xor y (.val (BitVec.intMin w)))
      (.val (BitVec.intMin w)) p.nsw p.nuw) ⊒ .int w y := by
  cases y <;> simp [LLVM.Int.add, LLVM.Int.xor, Id.run, pure,
    RuntimeValue.isRefinedBy, isRefinedBy]
  grind [xor_signmask_add]

/-- add nsw/nuw (xor Y,signmask),signmask → Y. -/
def pattern (n m : Int) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let y ← MatchProg.value ty
      let c ← matchBitConstant ty n
      let d ← matchBitConstant ty m
      let xr ← MatchProg.operation (.llvm .xor) #[y,c] #[ty]
      let _ ← MatchProg.root (.llvm .add) #[xr.res[0]!,d] #[ty] (fun p => p.nsw || p.nuw)
      MatchProg.matchNative ty (fun t => match t.val with
        | .integerType it => (BitVec.ofInt it.bitwidth n == BitVec.intMin it.bitwidth) &&
            (BitVec.ofInt it.bitwidth m == BitVec.intMin it.bitwidth)
        | _ => false)
      return y)
    pure (fun x => x)

theorem valid (n m : Int) : Pattern.Valid (pattern n m) := by
  simp only [pattern, matchBitConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ y cp cv hc dp dv hd xp xv hx p v hp hi hn hm hg
  obtain rfl := matched_bit_constant_eq _ cp n cv hc hn
  obtain rfl := matched_bit_constant_eq _ dp m dv hd hm
  obtain rfl := (xor_iff w xp y _ xv).mp hx
  obtain rfl := (add_iff w p _ _ v).mp hi
  change ((BitVec.ofInt w n == BitVec.intMin w) && (BitVec.ofInt w m == BitVec.intMin w)) = true at hg
  have hg' : BitVec.ofInt w n = BitVec.intMin w ∧ BitVec.ofInt w m = BitVec.intMin w := by simpa using hg
  rw [hg'.1,hg'.2]
  exact refines _ _
end Veir.InstSimplify.IS0633
