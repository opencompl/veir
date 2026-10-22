import Veir.InstSimplify.CmpSelectSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
/-- Pinned upstream scalar i1 comparison rule IS2959; all listed predicates. -/
def IS2959 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let x ← MatchProg.value ty
    let one ← matchIntConstant ty 1
    let inv ← MatchProg.operation (.llvm .xor) #[x,one] #[ty]
    let c ← matchIntConstant ty 1
    let _ ← MatchProg.root (.llvm .icmp) #[inv.res[0]!,c] #[ty] (fun p => p.predicate == .ne || p.predicate == .ult || p.predicate == .sgt)
    return x)
  pure
  (fun x => x)

theorem IS2959_valid : Pattern.Valid IS2959 := by
  simp only [IS2959, matchIntConstant]
  provePuddleValid
  rintro _ ⟨w,s⟩ rfl hw
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x
  rintro op ov oh oi
  obtain rfl := (matched_constant_iff _ _ 1 oh _).mp oi
  rintro xp xv xi
  obtain rfl := (xor_iff _ _ _ _ _).mp xi
  rintro cp cv hc hi ip iv hp hh
  have : w = 1 := by simpa using hw
  subst w
  obtain rfl := (matched_constant_iff _ _ _ hc _).mp hi
  obtain rfl := (icmp_iff _ _ _ _ _).mp hh
  rcases ip with ⟨p⟩
  simp only [Bool.or_eq_true, beq_iff_eq] at hp
  rcases int1_cases x with rfl | rfl | rfl <;>
    cases p <;> simp_all [LLVM.Int.xor, LLVM.Int.icmp, LLVM.IntPred.eval, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]
end Veir.InstSimplify
