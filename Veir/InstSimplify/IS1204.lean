import Veir.InstSimplify.ArithmeticExtra
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS1204
private theorem urem_mul_constant (x a b : BitVec w) (h : ¬x.umulOverflow a) (hm : a%b=0) : (x*a)%b=0 := by
  have hm' := congrArg BitVec.toNat hm
  simp only [BitVec.toNat_umod] at hm'
  change a.toNat % b.toNat = 0 at hm'
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_umod, BitVec.toNat_mul_of_not_umulOverflow h]
  have hz : (0 : BitVec w).toNat = 0 := rfl
  rw [hz, Nat.mul_mod, hm']
  simp
private theorem srem_mul_constant (x a b : BitVec w) (h : ¬x.smulOverflow a) (hm : a.srem b=0) : (x*a).srem b=0 := by
  have hm' := congrArg BitVec.toInt hm
  simp only [BitVec.toInt_srem] at hm'
  have hz : (0 : BitVec w).toInt = 0 := by simp
  rw [hz] at hm'
  have hd : b.toInt ∣ a.toInt := Int.dvd_of_tmod_eq_zero hm'
  apply BitVec.srem_zero_of_dvd
  rw [BitVec.toInt_mul_of_not_smulOverflow h]
  exact Int.dvd_trans hd (Int.dvd_mul_left _ _)

private theorem refines_srem (x : LLVM.Int w) (a b : BitVec w) (hm : a.srem b = 0) (nu : Bool) :
    RuntimeValue.int w (LLVM.Int.srem (LLVM.Int.mul x (.val a) true nu) (.val b)) ⊒ .int w (.val 0) := by
  cases x <;> simp [LLVM.Int.mul, LLVM.Int.srem, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
  grind [srem_mul_constant]

def pattern_srem (n m : Int) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let a ← matchBitConstant ty n
      let b ← matchBitConstant ty m
      let mul ← MatchProg.operation (.llvm .mul) #[x,a] #[ty] (fun p => p.nsw)
      let _ ← MatchProg.root (.llvm .srem) #[mul.res[0]!,b] #[ty]
      MatchProg.matchNative ty (fun t => match t.val with
        | .integerType it => ((BitVec.ofInt it.bitwidth n).srem (BitVec.ofInt it.bitwidth m)) == 0
        | _ => false)
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__zero) default
      CreateProg.operation (.llvm .mlir__zero) #[] #[ty] p)
    (fun r => r)

theorem pattern_srem_valid (n m : Int) : Pattern.Valid (pattern_srem n m) := by
  simp only [pattern_srem, matchBitConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x ap av ha bp bv hb mp mv hp hm rp rv hr hca hcb hg
  obtain rfl := matched_bit_constant_eq _ ap n av ha hca
  obtain rfl := matched_bit_constant_eq _ bp m bv hb hcb
  obtain rfl := (mul_iff w mp x _ mv).mp hm
  obtain ⟨hu,rfl⟩ := (srem_iff w rp _ _ rv).mp hr
  change (((BitVec.ofInt w n).srem (BitVec.ofInt w m)) == 0) = true at hg
  have hg' : (BitVec.ofInt w n).srem (BitVec.ofInt w m) = 0 := by simpa using hg
  exists (.int w (.val 0))
  constructor
  · exact (zero_iff _ _ _).mpr rfl
  · rw [hp]
    exact refines_srem _ _ _ hg' _

private theorem refines_urem (x : LLVM.Int w) (a b : BitVec w) (hm : a % b = 0) (ns : Bool) :
    RuntimeValue.int w (LLVM.Int.urem (LLVM.Int.mul x (.val a) ns true) (.val b)) ⊒ .int w (.val 0) := by
  cases x <;> simp [LLVM.Int.mul, LLVM.Int.urem, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
  grind [urem_mul_constant]

def pattern_urem (n m : Int) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let a ← matchBitConstant ty n
      let b ← matchBitConstant ty m
      let mul ← MatchProg.operation (.llvm .mul) #[x,a] #[ty] (fun p => p.nuw)
      let _ ← MatchProg.root (.llvm .urem) #[mul.res[0]!,b] #[ty]
      MatchProg.matchNative ty (fun t => match t.val with
        | .integerType it => ((BitVec.ofInt it.bitwidth n).umod (BitVec.ofInt it.bitwidth m)) == 0
        | _ => false)
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__zero) default
      CreateProg.operation (.llvm .mlir__zero) #[] #[ty] p)
    (fun r => r)

theorem pattern_urem_valid (n m : Int) : Pattern.Valid (pattern_urem n m) := by
  simp only [pattern_urem, matchBitConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x ap av ha bp bv hb mp mv hp hm rp rv hr hca hcb hg
  obtain rfl := matched_bit_constant_eq _ ap n av ha hca
  obtain rfl := matched_bit_constant_eq _ bp m bv hb hcb
  obtain rfl := (mul_iff w mp x _ mv).mp hm
  obtain ⟨hu,rfl⟩ := (urem_iff w rp _ _ rv).mp hr
  change (((BitVec.ofInt w n).umod (BitVec.ofInt w m)) == 0) = true at hg
  have hg' : (BitVec.ofInt w n).umod (BitVec.ofInt w m) = 0 := by simpa using hg
  exists (.int w (.val 0))
  constructor
  · exact (zero_iff _ _ _).mpr rfl
  · rw [hp]
    exact refines_urem _ _ _ hg' _
end Veir.InstSimplify.IS1204
