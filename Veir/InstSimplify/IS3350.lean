import Veir.InstSimplify.CmpSelectSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
/-- For every scalar width, odd `C-X` never equals `X`; both EQ and NE, with all overflow flags. -/
def IS3350 (constant : Int) (equal : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
      (fun t => (BitVec.ofInt t.bitwidth constant).getLsbD 0)
    let cty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let x ← MatchProg.value ty
    let c ← matchIntConstant ty constant
    let sub ← MatchProg.operation (.llvm .sub) #[c,x] #[ty]
    let _ ← MatchProg.root (.llvm .icmp) #[sub.res[0]!,x] #[cty]
      (fun p => p.predicate == (match equal with | true => .eq | false => .ne))
    return cty)
  (fun ty => do
    let p ← CreateProg.property (.llvm .mlir__constant)
      (LLVMConstantProperties.mk (.integer (IntegerAttr.mk
        (match equal with | true => 0 | false => 1) (IntegerType.signless 1))))
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
  (fun x => x)

theorem IS3350_valid (constant : Int) (equal : Bool) : Pattern.Valid (IS3350 constant equal) := by
  cases equal
  all_goals
    simp only [IS3350, matchIntConstant]
    provePuddleValid
    rintro _ ⟨w,s⟩ rfl hc _ ⟨cw,cs⟩ rfl hw
    have : cw = 1 := by simpa using hw
    subst cw
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x cp cv ch ci
    obtain rfl := (matched_constant_iff _ _ _ ch _).mp ci
    intro sp sv si
    obtain rfl := (sub_iff _ _ _ _ _).mp si
    intro ip iv ih ii
    obtain rfl := (icmp_iff _ _ _ _ _).mp ii
    refine ⟨_, (constant_iff _ _ _ rfl _).mpr rfl, ?_⟩
    have hp := ih
    try simp only [beq_iff_eq] at hp
    cases x with
    | poison => simp [LLVM.Int.sub, LLVM.Int.icmp, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
    | val x =>
      have hn := odd_sub_ne_self x (BitVec.ofInt w constant) hc
      have hn' : (BitVec.ofInt w constant - x == x) = false := beq_eq_false_iff_ne.mpr hn
      by_cases hs : sp.nsw = true ∧ (BitVec.ofInt w constant).ssubOverflow x = true <;>
        by_cases hu : sp.nuw = true ∧ (BitVec.ofInt w constant).usubOverflow x = true <;>
          simp [LLVM.Int.sub, LLVM.Int.icmp, LLVM.IntPred.eval, hp, hs, hu,
            Id.run, RuntimeValue.isRefinedBy, isRefinedBy, hn', bne]
end Veir.InstSimplify
