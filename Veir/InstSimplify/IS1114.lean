import Veir.InstSimplify.ArithmeticExtra
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS1114
private theorem udiv_mul_cancel (x y : BitVec w) (h : ¬x.umulOverflow y) (hy : y ≠ 0) : (x*y)/y=x := by
  apply BitVec.eq_of_toNat_eq
  have hy' : 0 < y.toNat := by
    have : y.toNat ≠ 0 := by intro h; apply hy; apply BitVec.eq_of_toNat_eq; simpa using h
    omega
  simp only [BitVec.toNat_udiv, BitVec.toNat_mul_of_not_umulOverflow h]
  exact Nat.mul_div_cancel x.toNat hy'
private theorem sdiv_mul_cancel (x y : BitVec w) (h : ¬x.smulOverflow y) (hy : y ≠ 0) : (x*y).sdiv y=x := by
  have hy' : y.toInt ≠ 0 := by intro he; apply hy; apply BitVec.eq_of_toInt_eq; simpa using he
  have hs : (x*y).sdiv y = BitVec.ofInt w ((x*y).toInt.tdiv y.toInt) := by
    apply BitVec.eq_of_toInt_eq
    simp only [BitVec.toInt_sdiv, BitVec.toInt_ofInt]
  rw [hs, BitVec.toInt_mul_of_not_smulOverflow h, Int.mul_tdiv_cancel _ hy', BitVec.ofInt_toInt]
private theorem urem_mul_cancel (x y : BitVec w) (h : ¬x.umulOverflow y) : (x*y)%y=0 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_umod, BitVec.toNat_mul_of_not_umulOverflow h]
  simp
private theorem srem_mul_cancel (x y : BitVec w) (h : ¬x.smulOverflow y) : (x*y).srem y=0 := by
  apply BitVec.srem_zero_of_dvd
  rw [BitVec.toInt_mul_of_not_smulOverflow h]
  exact Int.dvd_mul_left _ _

private theorem refines_sdiv (x y : LLVM.Int w) (nu : Bool) (ex : Bool) :
    RuntimeValue.int w (LLVM.Int.sdiv (LLVM.Int.mul x y true nu) y ex) ⊒ .int w x := by
  cases x <;> cases y <;> simp [LLVM.Int.sdiv, LLVM.Int.mul, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
  grind [sdiv_mul_cancel]

def pattern_sdiv : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let mul ← MatchProg.operation (.llvm .mul) #[x,y] #[ty] (fun p => p.nsw)
      let _ ← MatchProg.root (.llvm .sdiv) #[mul.res[0]!,y] #[ty]
      return x)
    pure (fun x => x)

theorem pattern_sdiv_valid : Pattern.Valid pattern_sdiv := by
  simp only [pattern_sdiv]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x y mp mv hp hm p v hi
  obtain rfl := (mul_iff w mp x y mv).mp hm
  obtain ⟨hu,rfl⟩ := (sdiv_iff w p _ y v).mp hi
  rw [hp]
  exact refines_sdiv _ _ _ _

def pattern_sdiv_commute : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let mul ← MatchProg.operation (.llvm .mul) #[y,x] #[ty] (fun p => p.nsw)
      let _ ← MatchProg.root (.llvm .sdiv) #[mul.res[0]!,y] #[ty]
      return x)
    pure (fun x => x)

theorem pattern_sdiv_commute_valid : Pattern.Valid pattern_sdiv_commute := by
  simp only [pattern_sdiv_commute]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x y mp mv hp hm p v hi
  obtain rfl := (mul_iff w mp y x mv).mp hm
  obtain ⟨hu,rfl⟩ := (sdiv_iff w p _ y v).mp hi
  rw [hp]
  rw [LLVM.Int.mul_comm]
  exact refines_sdiv _ _ _ _

private theorem refines_udiv (x y : LLVM.Int w) (ns : Bool) (ex : Bool) :
    RuntimeValue.int w (LLVM.Int.udiv (LLVM.Int.mul x y ns true) y ex) ⊒ .int w x := by
  cases x <;> cases y <;> simp [LLVM.Int.udiv, LLVM.Int.mul, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
  grind [udiv_mul_cancel]

def pattern_udiv : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let mul ← MatchProg.operation (.llvm .mul) #[x,y] #[ty] (fun p => p.nuw)
      let _ ← MatchProg.root (.llvm .udiv) #[mul.res[0]!,y] #[ty]
      return x)
    pure (fun x => x)

theorem pattern_udiv_valid : Pattern.Valid pattern_udiv := by
  simp only [pattern_udiv]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x y mp mv hp hm p v hi
  obtain rfl := (mul_iff w mp x y mv).mp hm
  obtain ⟨hu,rfl⟩ := (udiv_iff w p _ y v).mp hi
  rw [hp]
  exact refines_udiv _ _ _ _

def pattern_udiv_commute : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let mul ← MatchProg.operation (.llvm .mul) #[y,x] #[ty] (fun p => p.nuw)
      let _ ← MatchProg.root (.llvm .udiv) #[mul.res[0]!,y] #[ty]
      return x)
    pure (fun x => x)

theorem pattern_udiv_commute_valid : Pattern.Valid pattern_udiv_commute := by
  simp only [pattern_udiv_commute]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x y mp mv hp hm p v hi
  obtain rfl := (mul_iff w mp y x mv).mp hm
  obtain ⟨hu,rfl⟩ := (udiv_iff w p _ y v).mp hi
  rw [hp]
  rw [LLVM.Int.mul_comm]
  exact refines_udiv _ _ _ _

private theorem refines_srem (x y : LLVM.Int w) (nu : Bool)  :
    RuntimeValue.int w (LLVM.Int.srem (LLVM.Int.mul x y true nu) y ) ⊒ .int w (.val 0) := by
  cases x <;> cases y <;> simp [LLVM.Int.srem, LLVM.Int.mul, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
  grind [srem_mul_cancel]

def pattern_srem : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let mul ← MatchProg.operation (.llvm .mul) #[x,y] #[ty] (fun p => p.nsw)
      let _ ← MatchProg.root (.llvm .srem) #[mul.res[0]!,y] #[ty]
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__zero) default
      CreateProg.operation (.llvm .mlir__zero) #[] #[ty] p)
    (fun r => r)

theorem pattern_srem_valid : Pattern.Valid pattern_srem := by
  simp only [pattern_srem]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x y mp mv hp hm p v hi
  obtain rfl := (mul_iff w mp x y mv).mp hm
  obtain ⟨hu,rfl⟩ := (srem_iff w p _ y v).mp hi
  exists (.int w (.val 0))
  constructor
  · exact (zero_iff _ _ _).mpr rfl
  · rw [hp]
    exact refines_srem _ _ _

def pattern_srem_commute : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let mul ← MatchProg.operation (.llvm .mul) #[y,x] #[ty] (fun p => p.nsw)
      let _ ← MatchProg.root (.llvm .srem) #[mul.res[0]!,y] #[ty]
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__zero) default
      CreateProg.operation (.llvm .mlir__zero) #[] #[ty] p)
    (fun r => r)

theorem pattern_srem_commute_valid : Pattern.Valid pattern_srem_commute := by
  simp only [pattern_srem_commute]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x y mp mv hp hm p v hi
  obtain rfl := (mul_iff w mp y x mv).mp hm
  obtain ⟨hu,rfl⟩ := (srem_iff w p _ y v).mp hi
  exists (.int w (.val 0))
  constructor
  · exact (zero_iff _ _ _).mpr rfl
  · rw [hp]
    rw [LLVM.Int.mul_comm]
    exact refines_srem _ _ _

private theorem refines_urem (x y : LLVM.Int w) (ns : Bool)  :
    RuntimeValue.int w (LLVM.Int.urem (LLVM.Int.mul x y ns true) y ) ⊒ .int w (.val 0) := by
  cases x <;> cases y <;> simp [LLVM.Int.urem, LLVM.Int.mul, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
  grind [urem_mul_cancel]

def pattern_urem : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let mul ← MatchProg.operation (.llvm .mul) #[x,y] #[ty] (fun p => p.nuw)
      let _ ← MatchProg.root (.llvm .urem) #[mul.res[0]!,y] #[ty]
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__zero) default
      CreateProg.operation (.llvm .mlir__zero) #[] #[ty] p)
    (fun r => r)

theorem pattern_urem_valid : Pattern.Valid pattern_urem := by
  simp only [pattern_urem]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x y mp mv hp hm p v hi
  obtain rfl := (mul_iff w mp x y mv).mp hm
  obtain ⟨hu,rfl⟩ := (urem_iff w p _ y v).mp hi
  exists (.int w (.val 0))
  constructor
  · exact (zero_iff _ _ _).mpr rfl
  · rw [hp]
    exact refines_urem _ _ _

def pattern_urem_commute : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let mul ← MatchProg.operation (.llvm .mul) #[y,x] #[ty] (fun p => p.nuw)
      let _ ← MatchProg.root (.llvm .urem) #[mul.res[0]!,y] #[ty]
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__zero) default
      CreateProg.operation (.llvm .mlir__zero) #[] #[ty] p)
    (fun r => r)

theorem pattern_urem_commute_valid : Pattern.Valid pattern_urem_commute := by
  simp only [pattern_urem_commute]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x y mp mv hp hm p v hi
  obtain rfl := (mul_iff w mp y x mv).mp hm
  obtain ⟨hu,rfl⟩ := (urem_iff w p _ y v).mp hi
  exists (.int w (.val 0))
  constructor
  · exact (zero_iff _ _ _).mpr rfl
  · rw [hp]
    rw [LLVM.Int.mul_comm]
    exact refines_urem _ _ _
private theorem tdiv_mul_bounds_pos (a b : Int) (ha : 0 ≤ a) : 0 ≤ a.tdiv b * b ∧ a.tdiv b * b ≤ a := by
  constructor
  · by_cases hb : 0 ≤ b
    · exact Int.mul_nonneg (Int.tdiv_nonneg ha hb) hb
    · exact Int.mul_nonneg_of_nonpos_of_nonpos (Int.tdiv_nonpos_of_nonneg_of_nonpos ha (by omega)) (by omega)
  · rw [Int.mul_comm]
    exact Int.mul_tdiv_self_le ha
private theorem tdiv_mul_bounds (a b : Int) : min 0 a ≤ a.tdiv b * b ∧ a.tdiv b * b ≤ max 0 a := by
  by_cases ha : 0 ≤ a
  · have hh := tdiv_mul_bounds_pos a b ha
    simp only [Int.min_def, Int.max_def]
    split <;> omega
  · have hh := tdiv_mul_bounds_pos (-a) b (by omega)
    simp only [Int.neg_tdiv, Int.neg_mul] at hh
    simp only [Int.min_def, Int.max_def]
    split <;> omega
private theorem sdiv_mul_nooverflow (a y : BitVec w)
    (h : a ≠ BitVec.intMin w ∨ y ≠ -1#w) : ¬(a.sdiv y).smulOverflow y := by
  have hb := tdiv_mul_bounds a.toInt y.toInt
  have hl := BitVec.le_toInt a
  have hu := BitVec.toInt_lt (x := a)
  have hp : (0 : Int) < 2^(w-1) := by exact Int.pow_pos (by decide)
  simp only [BitVec.smulOverflow, BitVec.toInt_sdiv_of_ne_or_ne a y h,
    Bool.or_eq_true, decide_eq_true_eq, not_or]
  simp only [Int.min_def, Int.max_def] at hb
  split at hb <;> omega
private theorem udiv_mul_nooverflow (a y : BitVec w) : ¬(a/y).umulOverflow y := by
  have hb := Nat.div_mul_le_self a.toNat y.toNat
  have ha := a.isLt
  simp only [BitVec.umulOverflow, BitVec.toNat_udiv, decide_eq_true_eq]
  omega

private theorem quotient_refines_sdiv (a y : LLVM.Int w) (de : Bool) (mp : NswNuwProperties)
    (ex : Bool) (hub : LLVM.Int.isSignedDivisionUB a y = false) :
    RuntimeValue.int w (LLVM.Int.sdiv (LLVM.Int.mul (LLVM.Int.sdiv a y de) y mp.nsw mp.nuw) y ex) ⊒
      .int w (LLVM.Int.sdiv a y de) := by
  cases a <;> cases y <;> simp [LLVM.Int.sdiv, LLVM.Int.sdiv, LLVM.Int.mul, Id.run, pure,
    LLVM.Int.isSignedDivisionUB, LLVM.Int.isUnsignedDivisionUB, RuntimeValue.isRefinedBy, isRefinedBy] at *
  all_goals grind [sdiv_mul_nooverflow, sdiv_mul_cancel]

def pattern_quotient_sdiv : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value ty
      let y ← MatchProg.value ty
      let d ← MatchProg.operation (.llvm .sdiv) #[a,y] #[ty]
      let mul ← MatchProg.operation (.llvm .mul) #[d.res[0]!,y] #[ty]
      let _ ← MatchProg.root (.llvm .sdiv) #[mul.res[0]!,y] #[ty]
      return d.res[0]!)
    pure (fun x => x)

theorem pattern_quotient_sdiv_valid : Pattern.Valid pattern_quotient_sdiv := by
  simp only [pattern_quotient_sdiv]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ a y dp dv dh mp mv hm p v hi
  obtain ⟨hdub,rfl⟩ := (sdiv_iff w dp a y dv).mp dh
  obtain rfl := (mul_iff w mp _ y mv).mp hm
  obtain ⟨hu,rfl⟩ := (sdiv_iff w p _ y v).mp hi
  exact quotient_refines_sdiv _ _ _ _ _ hdub

def pattern_quotient_sdiv_commute : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value ty
      let y ← MatchProg.value ty
      let d ← MatchProg.operation (.llvm .sdiv) #[a,y] #[ty]
      let mul ← MatchProg.operation (.llvm .mul) #[y,d.res[0]!] #[ty]
      let _ ← MatchProg.root (.llvm .sdiv) #[mul.res[0]!,y] #[ty]
      return d.res[0]!)
    pure (fun x => x)

theorem pattern_quotient_sdiv_commute_valid : Pattern.Valid pattern_quotient_sdiv_commute := by
  simp only [pattern_quotient_sdiv_commute]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ a y dp dv dh mp mv hm p v hi
  obtain ⟨hdub,rfl⟩ := (sdiv_iff w dp a y dv).mp dh
  obtain rfl := (mul_iff w mp y _ mv).mp hm
  obtain ⟨hu,rfl⟩ := (sdiv_iff w p _ y v).mp hi
  rw [LLVM.Int.mul_comm]
  exact quotient_refines_sdiv _ _ _ _ _ hdub

private theorem quotient_refines_udiv (a y : LLVM.Int w) (de : Bool) (mp : NswNuwProperties)
    (ex : Bool) (hub : LLVM.Int.isUnsignedDivisionUB y = false) :
    RuntimeValue.int w (LLVM.Int.udiv (LLVM.Int.mul (LLVM.Int.udiv a y de) y mp.nsw mp.nuw) y ex) ⊒
      .int w (LLVM.Int.udiv a y de) := by
  cases a <;> cases y <;> simp [LLVM.Int.udiv, LLVM.Int.udiv, LLVM.Int.mul, Id.run, pure,
    LLVM.Int.isSignedDivisionUB, LLVM.Int.isUnsignedDivisionUB, RuntimeValue.isRefinedBy, isRefinedBy] at *
  all_goals grind [udiv_mul_nooverflow, udiv_mul_cancel]

def pattern_quotient_udiv : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value ty
      let y ← MatchProg.value ty
      let d ← MatchProg.operation (.llvm .udiv) #[a,y] #[ty]
      let mul ← MatchProg.operation (.llvm .mul) #[d.res[0]!,y] #[ty]
      let _ ← MatchProg.root (.llvm .udiv) #[mul.res[0]!,y] #[ty]
      return d.res[0]!)
    pure (fun x => x)

theorem pattern_quotient_udiv_valid : Pattern.Valid pattern_quotient_udiv := by
  simp only [pattern_quotient_udiv]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ a y dp dv dh mp mv hm p v hi
  obtain ⟨hdub,rfl⟩ := (udiv_iff w dp a y dv).mp dh
  obtain rfl := (mul_iff w mp _ y mv).mp hm
  obtain ⟨hu,rfl⟩ := (udiv_iff w p _ y v).mp hi
  exact quotient_refines_udiv _ _ _ _ _ hdub

def pattern_quotient_udiv_commute : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value ty
      let y ← MatchProg.value ty
      let d ← MatchProg.operation (.llvm .udiv) #[a,y] #[ty]
      let mul ← MatchProg.operation (.llvm .mul) #[y,d.res[0]!] #[ty]
      let _ ← MatchProg.root (.llvm .udiv) #[mul.res[0]!,y] #[ty]
      return d.res[0]!)
    pure (fun x => x)

theorem pattern_quotient_udiv_commute_valid : Pattern.Valid pattern_quotient_udiv_commute := by
  simp only [pattern_quotient_udiv_commute]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ a y dp dv dh mp mv hm p v hi
  obtain ⟨hdub,rfl⟩ := (udiv_iff w dp a y dv).mp dh
  obtain rfl := (mul_iff w mp y _ mv).mp hm
  obtain ⟨hu,rfl⟩ := (udiv_iff w p _ y v).mp hi
  rw [LLVM.Int.mul_comm]
  exact quotient_refines_udiv _ _ _ _ _ hdub

private theorem quotient_refines_srem (a y : LLVM.Int w) (de : Bool) (mp : NswNuwProperties)
     (hub : LLVM.Int.isSignedDivisionUB a y = false) :
    RuntimeValue.int w (LLVM.Int.srem (LLVM.Int.mul (LLVM.Int.sdiv a y de) y mp.nsw mp.nuw) y ) ⊒
      .int w (.val 0) := by
  cases a <;> cases y <;> simp [LLVM.Int.srem, LLVM.Int.sdiv, LLVM.Int.mul, Id.run, pure,
    LLVM.Int.isSignedDivisionUB, LLVM.Int.isUnsignedDivisionUB, RuntimeValue.isRefinedBy, isRefinedBy] at *
  all_goals grind [sdiv_mul_nooverflow, srem_mul_cancel]

def pattern_quotient_srem : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value ty
      let y ← MatchProg.value ty
      let d ← MatchProg.operation (.llvm .sdiv) #[a,y] #[ty]
      let mul ← MatchProg.operation (.llvm .mul) #[d.res[0]!,y] #[ty]
      let _ ← MatchProg.root (.llvm .srem) #[mul.res[0]!,y] #[ty]
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__zero) default
      CreateProg.operation (.llvm .mlir__zero) #[] #[ty] p)
    (fun r => r)

theorem pattern_quotient_srem_valid : Pattern.Valid pattern_quotient_srem := by
  simp only [pattern_quotient_srem]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ a y dp dv dh mp mv hm p v hi
  obtain ⟨hdub,rfl⟩ := (sdiv_iff w dp a y dv).mp dh
  obtain rfl := (mul_iff w mp _ y mv).mp hm
  obtain ⟨hu,rfl⟩ := (srem_iff w p _ y v).mp hi
  exists (.int w (.val 0))
  constructor
  · exact (zero_iff _ _ _).mpr rfl
  · exact quotient_refines_srem _ _ _ _ hdub

def pattern_quotient_srem_commute : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value ty
      let y ← MatchProg.value ty
      let d ← MatchProg.operation (.llvm .sdiv) #[a,y] #[ty]
      let mul ← MatchProg.operation (.llvm .mul) #[y,d.res[0]!] #[ty]
      let _ ← MatchProg.root (.llvm .srem) #[mul.res[0]!,y] #[ty]
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__zero) default
      CreateProg.operation (.llvm .mlir__zero) #[] #[ty] p)
    (fun r => r)

theorem pattern_quotient_srem_commute_valid : Pattern.Valid pattern_quotient_srem_commute := by
  simp only [pattern_quotient_srem_commute]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ a y dp dv dh mp mv hm p v hi
  obtain ⟨hdub,rfl⟩ := (sdiv_iff w dp a y dv).mp dh
  obtain rfl := (mul_iff w mp y _ mv).mp hm
  obtain ⟨hu,rfl⟩ := (srem_iff w p _ y v).mp hi
  exists (.int w (.val 0))
  constructor
  · exact (zero_iff _ _ _).mpr rfl
  · rw [LLVM.Int.mul_comm]
    exact quotient_refines_srem _ _ _ _ hdub

private theorem quotient_refines_urem (a y : LLVM.Int w) (de : Bool) (mp : NswNuwProperties)
     (hub : LLVM.Int.isUnsignedDivisionUB y = false) :
    RuntimeValue.int w (LLVM.Int.urem (LLVM.Int.mul (LLVM.Int.udiv a y de) y mp.nsw mp.nuw) y ) ⊒
      .int w (.val 0) := by
  cases a <;> cases y <;> simp [LLVM.Int.urem, LLVM.Int.udiv, LLVM.Int.mul, Id.run, pure,
    LLVM.Int.isSignedDivisionUB, LLVM.Int.isUnsignedDivisionUB, RuntimeValue.isRefinedBy, isRefinedBy] at *
  all_goals grind [udiv_mul_nooverflow, urem_mul_cancel]

def pattern_quotient_urem : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value ty
      let y ← MatchProg.value ty
      let d ← MatchProg.operation (.llvm .udiv) #[a,y] #[ty]
      let mul ← MatchProg.operation (.llvm .mul) #[d.res[0]!,y] #[ty]
      let _ ← MatchProg.root (.llvm .urem) #[mul.res[0]!,y] #[ty]
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__zero) default
      CreateProg.operation (.llvm .mlir__zero) #[] #[ty] p)
    (fun r => r)

theorem pattern_quotient_urem_valid : Pattern.Valid pattern_quotient_urem := by
  simp only [pattern_quotient_urem]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ a y dp dv dh mp mv hm p v hi
  obtain ⟨hdub,rfl⟩ := (udiv_iff w dp a y dv).mp dh
  obtain rfl := (mul_iff w mp _ y mv).mp hm
  obtain ⟨hu,rfl⟩ := (urem_iff w p _ y v).mp hi
  exists (.int w (.val 0))
  constructor
  · exact (zero_iff _ _ _).mpr rfl
  · exact quotient_refines_urem _ _ _ _ hdub

def pattern_quotient_urem_commute : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value ty
      let y ← MatchProg.value ty
      let d ← MatchProg.operation (.llvm .udiv) #[a,y] #[ty]
      let mul ← MatchProg.operation (.llvm .mul) #[y,d.res[0]!] #[ty]
      let _ ← MatchProg.root (.llvm .urem) #[mul.res[0]!,y] #[ty]
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__zero) default
      CreateProg.operation (.llvm .mlir__zero) #[] #[ty] p)
    (fun r => r)

theorem pattern_quotient_urem_commute_valid : Pattern.Valid pattern_quotient_urem_commute := by
  simp only [pattern_quotient_urem_commute]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ a y dp dv dh mp mv hm p v hi
  obtain ⟨hdub,rfl⟩ := (udiv_iff w dp a y dv).mp dh
  obtain rfl := (mul_iff w mp y _ mv).mp hm
  obtain ⟨hu,rfl⟩ := (urem_iff w p _ y v).mp hi
  exists (.int w (.val 0))
  constructor
  · exact (zero_iff _ _ _).mpr rfl
  · rw [LLVM.Int.mul_comm]
    exact quotient_refines_urem _ _ _ _ hdub
end Veir.InstSimplify.IS1114
