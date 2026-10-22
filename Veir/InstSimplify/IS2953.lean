import Veir.InstSimplify.CmpSelectSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
/-- Pinned upstream scalar i1 comparison rule IS2953; all listed predicates. -/
def IS2953 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let x ← MatchProg.value ty
    let c ← matchIntConstant ty 1
    let _ ← MatchProg.root (.llvm .icmp) #[x,c] #[ty] (fun p => p.predicate == .eq || p.predicate == .uge || p.predicate == .sle)
    return x)
  pure
  (fun x => x)

theorem IS2953_valid : Pattern.Valid IS2953 := by
  simp only [IS2953, matchIntConstant]
  provePuddleValid
  rintro _ ⟨w,s⟩ rfl hw
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro x cp cv hc hi ip iv hp hh
  have : w = 1 := by simpa using hw
  subst w
  obtain rfl := (matched_constant_iff _ _ _ hc _).mp hi
  obtain rfl := (icmp_iff _ _ _ _ _).mp hh
  rcases ip with ⟨p⟩
  simp only [Bool.or_eq_true, beq_iff_eq] at hp
  rcases int1_cases x with rfl | rfl | rfl <;>
    cases p <;> simp_all [LLVM.Int.icmp, LLVM.IntPred.eval, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]
end Veir.InstSimplify
