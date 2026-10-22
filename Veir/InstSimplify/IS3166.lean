import Veir.InstSimplify.CmpSelectSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 8000000
/-- Equality of a nonoverflowing constant product to a nonmultiple; both signed and unsigned guards. -/
def IS3166 (multiplier constant : Int) (unsigned equal : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun t =>
      let m := BitVec.ofInt t.bitwidth multiplier
      let c := BitVec.ofInt t.bitwidth constant
      m != 0 && (match unsigned with | true => c % m != 0 | false => c.srem m != 0))
    let cty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let x ← MatchProg.value ty
    let m ← matchIntConstant ty multiplier
    let c ← matchIntConstant ty constant
    let mul ← MatchProg.operation (.llvm .mul) #[x,m] #[ty]
      (fun p => match unsigned with | true => p.nuw | false => p.nsw)
    let _ ← MatchProg.root (.llvm .icmp) #[mul.res[0]!,c] #[cty]
      (fun p => p.predicate == (match equal with | true => .eq | false => .ne))
    return cty)
  (fun ty => do
    let p ← CreateProg.property (.llvm .mlir__constant)
      (LLVMConstantProperties.mk (.integer (IntegerAttr.mk
        (match equal with | true => 0 | false => 1) (IntegerType.signless 1))))
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
  (fun x => x)

theorem IS3166_valid (multiplier constant : Int) (unsigned equal : Bool) :
    Pattern.Valid (IS3166 multiplier constant unsigned equal) := by
  cases unsigned <;> cases equal
  all_goals
    simp only [IS3166, matchIntConstant]
    provePuddleValid
    rintro _ ⟨w,s⟩ rfl hm hc _ ⟨cw,cs⟩ rfl hw
    have : cw = 1 := by simpa using hw
    subst cw
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x mp mv mh mi
    obtain rfl := (matched_constant_iff _ _ _ mh _).mp mi
    intro cp cv ch ci
    obtain rfl := (matched_constant_iff _ _ _ ch _).mp ci
    intro ap av ah ai
    obtain rfl := (mul_iff _ _ _ _ _).mp ai
    intro ip iv ih ii
    obtain rfl := (icmp_iff _ _ _ _ _).mp ii
    refine ⟨_, (constant_iff _ _ _ rfl _).mpr rfl, ?_⟩
    have hp := ih
    try simp only [beq_iff_eq] at hp
    cases x with
    | poison => simp [LLVM.Int.mul, LLVM.Int.icmp, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
    | val x =>
      first
      | have hnr : (BitVec.ofInt w constant) % (BitVec.ofInt w multiplier) ≠ 0#w := by simpa using hc
        have hn : x.umulOverflow (BitVec.ofInt w multiplier) = false →
            (x * BitVec.ofInt w multiplier == BitVec.ofInt w constant) = false := by
          intro ho
          apply beq_eq_false_iff_ne.mpr
          intro he
          have hz := cmp_urem_mul_self x (BitVec.ofInt w multiplier) (by simp [ho])
          rw [he] at hz
          exact hnr hz
        cases hu : x.umulOverflow (BitVec.ofInt w multiplier) <;>
          cases hs : x.smulOverflow (BitVec.ofInt w multiplier) <;>
          cases hnsw : ap.nsw <;> cases hnuw : ap.nuw <;>
          (try simp [hnsw, hnuw] at ah) <;>
          simp [LLVM.Int.mul, LLVM.Int.icmp, LLVM.IntPred.eval, hp, bne,
            hu, hs, hnsw, hnuw, hn, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
      | have hnr : (BitVec.ofInt w constant).srem (BitVec.ofInt w multiplier) ≠ 0#w := by simpa using hc
        have hn : x.smulOverflow (BitVec.ofInt w multiplier) = false →
            (x * BitVec.ofInt w multiplier == BitVec.ofInt w constant) = false := by
          intro ho
          apply beq_eq_false_iff_ne.mpr
          intro he
          have hz := cmp_srem_mul_self x (BitVec.ofInt w multiplier) (by simp [ho])
          rw [he] at hz
          exact hnr hz
        cases hu : x.umulOverflow (BitVec.ofInt w multiplier) <;>
          cases hs : x.smulOverflow (BitVec.ofInt w multiplier) <;>
          cases hnsw : ap.nsw <;> cases hnuw : ap.nuw <;>
          (try simp [hnsw, hnuw] at ah) <;>
          simp [LLVM.Int.mul, LLVM.Int.icmp, LLVM.IntPred.eval, hp, bne,
            hu, hs, hnsw, hnuw, hn, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
end Veir.InstSimplify
