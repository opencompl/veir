import Veir.InstSimplify.ArithmeticSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS0621
/-- X + (Y-X) → Y; either order of the outer add, all flags. -/
def pattern (commute : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let sub ← MatchProg.operation (.llvm .sub) #[y,x] #[ty]
      let _ ← MatchProg.root (.llvm .add)
        (if commute then #[sub.res[0]!, x] else #[x, sub.res[0]!]) #[ty]
      return y)
    pure (fun x => x)

private theorem cancel (x y : LLVM.Int w) (a b c d : Bool) :
    RuntimeValue.int w (LLVM.Int.add x (LLVM.Int.sub y x a b) c d) ⊒ .int w y := by
  cases x <;> cases y <;>
    simp [LLVM.Int.add, LLVM.Int.sub, Id.run, pure,
      RuntimeValue.isRefinedBy, isRefinedBy]
  grind [BitVec.add_sub_cancel]

private theorem cancel' (x y : LLVM.Int w) (a b c d : Bool) :
    RuntimeValue.int w (LLVM.Int.add (LLVM.Int.sub y x a b) x c d) ⊒ .int w y := by
  cases x <;> cases y <;>
    simp [LLVM.Int.add, LLVM.Int.sub, Id.run, pure,
      RuntimeValue.isRefinedBy, isRefinedBy]
  grind [BitVec.sub_add_cancel]

theorem valid (commute : Bool) : Pattern.Valid (pattern commute) := by
  cases commute <;> simp only [pattern, Bool.false_eq_true, ↓reduceIte]
  all_goals
    provePuddleValid
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    rintro ⟨w,s⟩ x y sp sv hs ap av ha
    obtain rfl := (sub_iff w sp y x sv).mp hs
    first
    | obtain rfl := (add_iff w ap x _ av).mp ha
      exact cancel _ _ _ _ _ _
    | obtain rfl := (add_iff w ap _ x av).mp ha
      exact cancel' _ _ _ _ _ _
end Veir.InstSimplify.IS0621
