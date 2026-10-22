import Veir.InstSimplify.FunnelExtra
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
/-- Complementary raw shifts reconstructed by either funnel intrinsic. -/
def IS7480 (left : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x ← MatchProg.value ty
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let c ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    MatchProg.matchNative (ty,a.properties,b.properties,c.properties) (fun (t,a,b,c) =>
      match t.val,a.value,b.value,c.value with
      | .integerType w,.integer a,.integer b,.integer c =>
        let av := BitVec.ofInt w.bitwidth a.value
        let bv := BitVec.ofInt w.bitwidth b.value
        let sh := (BitVec.ofInt w.bitwidth c.value).toNat % w.bitwidth
        (sh != 0) && (av+bv == BitVec.ofNat w.bitwidth w.bitwidth) &&
          (sh == (match left with | true => av | false => bv).toNat)
      | _,_,_,_ => false)
    let l ← MatchProg.operation (.llvm .lshr) #[x,a.res[0]!] #[ty]
    let r ← MatchProg.operation (.llvm .shl) #[x,b.res[0]!] #[ty]
    let _ ← MatchProg.root (.llvm (match left with | true => Llvm.intr__fshl | false => .intr__fshr)) #[l.res[0]!,r.res[0]!,c.res[0]!] #[ty]
    return x)
  pure (fun x => x)
theorem IS7480_valid (left : Bool) : Pattern.Valid (IS7480 left) := by
  cases left
  all_goals
    simp only [IS7480]
    provePuddleValid
    rintro ⟨w,s⟩
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    rintro x ap av ai bp bv bi cp cv ci lp lv li sp sv si rp rv ri hn
    obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ _ _ ai
    obtain ⟨b,hb,rfl⟩ := intrinsic_constant_success _ _ _ bi
    obtain ⟨c,hc,rfl⟩ := intrinsic_constant_success _ _ _ ci
    simp [TypeAttr.of_val,Attribute.of,-Attribute.integerType_eq_of,ha,hb,hc] at hn
    obtain ⟨⟨_,hab⟩,hs⟩ := hn
    obtain rfl := (lshr_iff _ _ _ _ _).mp li
    obtain rfl := (shl_iff _ _ _ _ _).mp si
    first
    | obtain rfl := (fshl_iff _ _ _ _ _ _).mp ri
    | obtain rfl := (fshr_iff _ _ _ _ _ _).mp ri
    first
    | exact funnel_recombine_semantic false x _ _ _ lp.exact sp.nsw sp.nuw hab hs
    | exact funnel_recombine_semantic true x _ _ _ lp.exact sp.nsw sp.nuw hab hs
end Veir.InstSimplify
