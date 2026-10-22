import Veir.InstSimplify.LogicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS0626
private theorem add_not_refines (x : LLVM.Int w) (a b : Bool) :
    RuntimeValue.int w (LLVM.Int.add x (LLVM.Int.xor x (.val (BitVec.ofInt w (-1)))) a b) ⊒
      .int w (.val (BitVec.ofInt w (-1))) := by
  have h : BitVec.ofInt w (-1) = BitVec.allOnes w := by
    rw [BitVec.ofInt_neg]; simp [BitVec.neg_one_eq_allOnes]
  cases x <;> simp [LLVM.Int.add, LLVM.Int.xor, Id.run, pure, h,
    RuntimeValue.isRefinedBy, isRefinedBy]
  grind [BitVec.neg_eq_not_add]

private theorem xor_comm (x y : LLVM.Int w) : LLVM.Int.xor x y = LLVM.Int.xor y x := by
  cases x <;> cases y <;> simp [LLVM.Int.xor, Id.run, BitVec.xor_comm]

private theorem add_comm_flags (x y : LLVM.Int w) (a b : Bool) :
    LLVM.Int.add x y a b = LLVM.Int.add y x a b := by
  cases x <;> cases y <;> simp [LLVM.Int.add, Id.run, pure, BitVec.add_comm,
    BitVec.saddOverflow_comm, BitVec.uaddOverflow_comm]

/-- X + ~X → -1, canonical all-ones constant, selected operand orders. -/
def pattern_00 : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchBitConstant ty (-1)
      let nt ← MatchProg.operation (.llvm .xor) #[x,c] #[ty]
      let _ ← MatchProg.root (.llvm .add) #[x,nt.res[0]!] #[ty]
      return c)
    pure (fun x => x)

theorem pattern_00_valid : Pattern.Valid pattern_00 := by
  simp only [pattern_00, matchBitConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc xp xv hx ap av ha hz
  obtain rfl := matched_bit_constant_eq _ cp (-1) cv hc hz
  obtain rfl := (xor_iff w xp x _ xv).mp hx
  obtain rfl := (add_iff w ap x _ av).mp ha
  exact add_not_refines _ _ _

/-- X + ~X → -1, canonical all-ones constant, selected operand orders. -/
def pattern_01 : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchBitConstant ty (-1)
      let nt ← MatchProg.operation (.llvm .xor) #[c,x] #[ty]
      let _ ← MatchProg.root (.llvm .add) #[x,nt.res[0]!] #[ty]
      return c)
    pure (fun x => x)

theorem pattern_01_valid : Pattern.Valid pattern_01 := by
  simp only [pattern_01, matchBitConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc xp xv hx ap av ha hz
  obtain rfl := matched_bit_constant_eq _ cp (-1) cv hc hz
  obtain rfl := (xor_iff w xp _ x xv).mp hx
  obtain rfl := (add_iff w ap x _ av).mp ha
  rw [xor_comm]
  exact add_not_refines _ _ _

/-- X + ~X → -1, canonical all-ones constant, selected operand orders. -/
def pattern_10 : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchBitConstant ty (-1)
      let nt ← MatchProg.operation (.llvm .xor) #[x,c] #[ty]
      let _ ← MatchProg.root (.llvm .add) #[nt.res[0]!,x] #[ty]
      return c)
    pure (fun x => x)

theorem pattern_10_valid : Pattern.Valid pattern_10 := by
  simp only [pattern_10, matchBitConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc xp xv hx ap av ha hz
  obtain rfl := matched_bit_constant_eq _ cp (-1) cv hc hz
  obtain rfl := (xor_iff w xp x _ xv).mp hx
  obtain rfl := (add_iff w ap _ x av).mp ha
  rw [add_comm_flags]
  exact add_not_refines _ _ _

/-- X + ~X → -1, canonical all-ones constant, selected operand orders. -/
def pattern_11 : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchBitConstant ty (-1)
      let nt ← MatchProg.operation (.llvm .xor) #[c,x] #[ty]
      let _ ← MatchProg.root (.llvm .add) #[nt.res[0]!,x] #[ty]
      return c)
    pure (fun x => x)

theorem pattern_11_valid : Pattern.Valid pattern_11 := by
  simp only [pattern_11, matchBitConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc xp xv hx ap av ha hz
  obtain rfl := matched_bit_constant_eq _ cp (-1) cv hc hz
  obtain rfl := (xor_iff w xp _ x xv).mp hx
  obtain rfl := (add_iff w ap _ x av).mp ha
  rw [xor_comm, add_comm_flags]
  exact add_not_refines _ _ _
end Veir.InstSimplify.IS0626
