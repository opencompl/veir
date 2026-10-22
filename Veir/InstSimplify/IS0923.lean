import Veir.InstSimplify.ArithmeticExtra
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS0923
private theorem udiv_mul_exact (x y : BitVec w) (h : x % y = 0) : (x / y) * y = x := by
  have hm := congrArg BitVec.toNat h
  simp only [BitVec.toNat_umod, BitVec.toNat_zero] at hm
  change x.toNat % y.toNat = 0 at hm
  have hd := Nat.mod_add_div x.toNat y.toNat
  rw [hm, Nat.zero_add, Nat.mul_comm] at hd
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_udiv, hd, Nat.mod_eq_of_lt x.isLt]
private theorem sdiv_mul_exact (x y : BitVec w) (h : x.smod y = 0) : (x.sdiv y) * y = x := by
  have hm := congrArg BitVec.toInt h
  simp only [BitVec.toInt_smod, BitVec.toInt_zero] at hm
  have hz : (0 : BitVec w).toInt = 0 := by simp
  rw [hz] at hm
  have hd : y.toInt ∣ x.toInt := Int.dvd_of_fmod_eq_zero hm
  have hr := Int.tdiv_mul_cancel hd
  have hs : x.sdiv y = BitVec.ofInt w (x.toInt.tdiv y.toInt) := by
    apply BitVec.eq_of_toInt_eq
    simp only [BitVec.toInt_sdiv, BitVec.toInt_ofInt]
  rw [hs, ← BitVec.ofInt_toInt (x := y), ← BitVec.ofInt_mul]
  rw [BitVec.ofInt_toInt, hr, BitVec.ofInt_toInt]

private theorem refines_udiv (x y : LLVM.Int w) (p : NswNuwProperties) :
    RuntimeValue.int w (LLVM.Int.mul (LLVM.Int.udiv x y true) y p.nsw p.nuw) ⊒ .int w x := by
  cases x <;> cases y <;> simp [LLVM.Int.udiv, LLVM.Int.mul, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
  grind [udiv_mul_exact]

def pattern_udiv : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let d ← MatchProg.operation (.llvm .udiv) #[x,y] #[ty] (fun p => p.exact)
      let _ ← MatchProg.root (.llvm .mul) #[d.res[0]!,y] #[ty]
      return x)
    pure (fun x => x)

theorem pattern_udiv_valid : Pattern.Valid pattern_udiv := by
  simp only [pattern_udiv]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x y dp dv de dh p v hi
  obtain ⟨hu,rfl⟩ := (udiv_iff w dp x y dv).mp dh
  obtain rfl := (mul_iff w p _ y v).mp hi
  rw [de]
  exact refines_udiv _ _ _

def pattern_udiv_left : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let d ← MatchProg.operation (.llvm .udiv) #[x,y] #[ty] (fun p => p.exact)
      let _ ← MatchProg.root (.llvm .mul) #[y,d.res[0]!] #[ty]
      return x)
    pure (fun x => x)

theorem pattern_udiv_left_valid : Pattern.Valid pattern_udiv_left := by
  simp only [pattern_udiv_left]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x y dp dv de dh p v hi
  obtain ⟨hu,rfl⟩ := (udiv_iff w dp x y dv).mp dh
  obtain rfl := (mul_iff w p y _ v).mp hi
  rw [de]
  rw [LLVM.Int.mul_comm]
  exact refines_udiv _ _ _

private theorem refines_sdiv (x y : LLVM.Int w) (p : NswNuwProperties) :
    RuntimeValue.int w (LLVM.Int.mul (LLVM.Int.sdiv x y true) y p.nsw p.nuw) ⊒ .int w x := by
  cases x <;> cases y <;> simp [LLVM.Int.sdiv, LLVM.Int.mul, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
  grind [sdiv_mul_exact]

def pattern_sdiv : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let d ← MatchProg.operation (.llvm .sdiv) #[x,y] #[ty] (fun p => p.exact)
      let _ ← MatchProg.root (.llvm .mul) #[d.res[0]!,y] #[ty]
      return x)
    pure (fun x => x)

theorem pattern_sdiv_valid : Pattern.Valid pattern_sdiv := by
  simp only [pattern_sdiv]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x y dp dv de dh p v hi
  obtain ⟨hu,rfl⟩ := (sdiv_iff w dp x y dv).mp dh
  obtain rfl := (mul_iff w p _ y v).mp hi
  rw [de]
  exact refines_sdiv _ _ _

def pattern_sdiv_left : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let d ← MatchProg.operation (.llvm .sdiv) #[x,y] #[ty] (fun p => p.exact)
      let _ ← MatchProg.root (.llvm .mul) #[y,d.res[0]!] #[ty]
      return x)
    pure (fun x => x)

theorem pattern_sdiv_left_valid : Pattern.Valid pattern_sdiv_left := by
  simp only [pattern_sdiv_left]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x y dp dv de dh p v hi
  obtain ⟨hu,rfl⟩ := (sdiv_iff w dp x y dv).mp dh
  obtain rfl := (mul_iff w p y _ v).mp hi
  rw [de]
  rw [LLVM.Int.mul_comm]
  exact refines_sdiv _ _ _
end Veir.InstSimplify.IS0923
