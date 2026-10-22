import Veir.InstSimplify.IntrinsicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
/-- Effective zero shift, using the APInt shift amount modulo its scalar bit width. -/
def IS7471 (left : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.value ty
    let b ← MatchProg.value ty
    let c ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    MatchProg.matchNative (ty,c.properties) (fun (t,p) => match t.val,p.value with
      | .integerType w, .integer attr => (BitVec.ofInt w.bitwidth attr.value).toNat % w.bitwidth == 0
      | _,_ => false)
    let _ ← MatchProg.root (.llvm (match left with | true => Llvm.intr__fshl | false => .intr__fshr)) #[a,b,c.res[0]!] #[ty]
    return (match left with | true => a | false => b))
  pure (fun x => x)
theorem IS7471_valid (left : Bool) : Pattern.Valid (IS7471 left) := by
  cases left
  all_goals
    simp only [IS7471]
    provePuddleValid
    rintro ⟨w,s⟩
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro a b
    rintro cp cv ci rp rv ri hc
    cases hp : cp.value <;> simp [TypeAttr.of_val, Attribute.of, -Attribute.integerType_eq_of, hp, Bool.false_eq_true] at hc
    case integer attr =>
      have hc : (BitVec.ofInt w attr.value).toNat % w = 0 := by simpa [Attribute.of] using hc
      obtain rfl := (constant_iff ⟨w,s⟩ cp attr hp _).mp ci
      first
      | obtain rfl := (fshl_iff _ _ _ _ _ _).mp ri
      | obtain rfl := (fshr_iff _ _ _ _ _ _).mp ri
      cases a <;> cases b
      all_goals
        simp only [LLVM.Int.fshl, LLVM.Int.fshr, Id.run, pure]
        try simp only [hc]
        simp [BitVec.extractLsb'_append_eq_left, BitVec.setWidth_append_eq_right, funnel_left_zero_shift, funnel_right_zero_shift,
          RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
end Veir.InstSimplify
