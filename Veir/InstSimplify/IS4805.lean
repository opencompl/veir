import Veir.InstSimplify.CmpSelectSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
/-- Scalar min/max intrinsic-select rewrite; arbitrary width and commutative intrinsic order. -/
def IS4805 (kind : MinMaxKind) (commute swapCmp swapArms : Bool) (inclusive : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let cty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let x ← MatchProg.value ty
    let y ← MatchProg.value ty
    let mm ← MatchProg.operation (.llvm kind.op)
      (match commute with | true => #[y,x] | false => #[x,y]) #[ty]
    let c ← MatchProg.operation (.llvm .icmp)
      (match swapCmp with | true => #[y,x] | false => #[x,y]) #[cty]
      (fun p => p.predicate == canonicalCmpPred (match inclusive with | true => kind.inverseNonStrictPred | false => kind.inverseStrictPred) swapCmp swapArms)
    let _ ← MatchProg.root (.llvm .select)
      (match swapArms with | true => #[c.res[0]!,mm.res[0]!,x] | false => #[c.res[0]!,x,mm.res[0]!]) #[ty]
    return x)
  pure (fun x => x)

theorem IS4805_valid (kind : MinMaxKind) (commute swapCmp swapArms : Bool) (inclusive : Bool) : Pattern.Valid (IS4805 kind commute swapCmp swapArms inclusive) := by
  cases commute <;> cases swapCmp <;> cases swapArms
  all_goals
    simp only [IS4805]
    unfoldPuddleBuilder
    constructor
    · cases kind <;> simp only [MinMaxKind.op] <;> provePuddleSupported
    · cbv
    · open scoped PuddleCbv in cbv
    simpPuddleSemantics
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    rintro ⟨w,s⟩ _ ⟨cw,cs⟩ rfl hw x y mp mv mi cp cv ch ci rp rv ri
    have : cw = 1 := by simpa using hw
    subst cw
    obtain rfl := (minmax_iff kind _ _ _ _ _).mp mi
    obtain rfl := (icmp_iff _ _ _ _ _).mp ci
    obtain rfl := (select_iff _ _ _ _ _ _).mp ri
    have hp := ch
    try simp only [beq_iff_eq] at hp
    cases x <;> cases y <;> cases kind <;> cases inclusive <;>
      simp [canonicalCmpPred, swapCmpPred, invertCmpPred, MinMaxKind.eval, MinMaxKind.strictPred, MinMaxKind.nonStrictPred,
        MinMaxKind.inverseStrictPred, MinMaxKind.inverseNonStrictPred,
        LLVM.Int.smax, LLVM.Int.smin, LLVM.Int.umax, LLVM.Int.umin,
        LLVM.Int.icmp, LLVM.Int.select, LLVM.IntPred.eval, hp,
        RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]
    all_goals first | (split <;> simp_all [RuntimeValue.isRefinedBy, isRefinedBy]) | skip
    all_goals try simp_all [BitVec.sle, BitVec.slt, BitVec.ule, BitVec.ult]
    all_goals grind [BitVec.toInt_inj, BitVec.toNat_inj]
end Veir.InstSimplify
