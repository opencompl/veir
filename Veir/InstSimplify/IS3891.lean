import Veir.InstSimplify.CmpSelectSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 8000000
/-- All modeled scalar integer constants, zero markers and poison constants; every width/predicate. -/
def IS3891 (width : Nat) (pred : LLVM.IntPred) (lhs rhs : ScalarLiteral) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == width)
    let cty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let a ← matchScalarLiteral ty lhs
    let b ← matchScalarLiteral ty rhs
    let _ ← MatchProg.root (.llvm .icmp) #[a,b] #[cty] (fun p => p.predicate == pred)
    return cty)
  (fun ty => createScalarLiteral ty (foldCmpLiteral pred width lhs rhs))
  (fun x => x)

theorem IS3891_valid (width : Nat) (pred : LLVM.IntPred) (lhs rhs : ScalarLiteral) :
    Pattern.Valid (IS3891 width pred lhs rhs) := by
  cases lhs <;> cases rhs
  all_goals
    simp only [IS3891, matchScalarLiteral, createScalarLiteral, foldCmpLiteral,
      matchIntConstant, matchZero, matchPoison]
    provePuddleValid
    rintro _ ⟨w,s⟩ rfl hw _ ⟨cw,cs⟩ rfl hc
    have : w = width := by simpa using hw
    subst w
    have : cw = 1 := by simpa using hc
    subst cw
    first
    | rintro ap av ah ai
      obtain rfl := (matched_constant_iff _ _ _ ah _).mp ai
    | rintro ap av ai
      first | obtain rfl := (zero_iff _ _ _).mp ai
            | obtain rfl := (poison_iff _ _ _).mp ai
    first
    | rintro bp bv bh bi
      obtain rfl := (matched_constant_iff _ _ _ bh _).mp bi
    | rintro bp bv bi
      first | obtain rfl := (zero_iff _ _ _).mp bi
            | obtain rfl := (poison_iff _ _ _).mp bi
    rintro ip iv ih ii
    obtain rfl := (icmp_iff _ _ _ _ _).mp ii
    have hp : ip.predicate = pred := by simpa using ih
    first
    | refine ⟨_, (constant_iff _ _ _ rfl _).mpr rfl, ?_⟩
      simp [LLVM.Int.icmp, Id.run, pure, hp, RuntimeValue.isRefinedBy, isRefinedBy, bool_bit_integer]
    | refine ⟨_, (poison_iff _ _ _).mpr rfl, ?_⟩
      simp [LLVM.Int.icmp, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
end Veir.InstSimplify
