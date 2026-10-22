import Veir.InstSimplify.MiscSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
/-- Recover a value from a truncation whose appropriate no-wrap flag promises preservation. -/
def IS5722 (signed : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let wide ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let narrow ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    MatchProg.matchNative (wide,narrow) (fun (w,n) => match w.val,n.val with
      | .integerType w, .integerType n => n.bitwidth < w.bitwidth
      | _,_ => false)
    let x ← MatchProg.value wide
    let t ← MatchProg.operation (.llvm .trunc) #[x] #[narrow]
      (fun p => match signed with | true => p.nsw | false => p.nuw)
    let _ ← MatchProg.root (.llvm (match signed with | true => Llvm.sext | false => .zext)) t.res #[wide]
    return x)
  pure (fun x => x)
theorem IS5722_valid (signed : Bool) : Pattern.Valid (IS5722 signed) := by
  cases signed
  all_goals
    simp only [IS5722]
    provePuddleValid
    rintro ⟨w,s⟩ ⟨n,ns⟩
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x
    rintro tp tv th ti rp rv ri hw
    have hw : n < w := by simpa [TypeAttr.of_val, Attribute.of, -Attribute.integerType_eq_of] using hw
    obtain rfl := (misc_trunc_iff ⟨w,s⟩ ⟨n,ns⟩ _ _ _ hw).mp ti
    first
    | obtain rfl := (misc_zext_iff ⟨n,ns⟩ ⟨w,s⟩ _ _ _ hw).mp ri
    | obtain rfl := (sext_iff ⟨n,ns⟩ ⟨w,s⟩ _ _ _ hw).mp ri
    cases x with
    | poison => simp [LLVM.Int.trunc, LLVM.Int.zext, LLVM.Int.sext, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
    | val x =>
      by_cases hs : tp.nsw = true ∧ (x.truncate n).signExtend w ≠ x
      all_goals
        by_cases hu : tp.nuw = true ∧ (x.truncate n).zeroExtend w ≠ x
        all_goals
          simp_all [LLVM.Int.trunc, LLVM.Int.zext, LLVM.Int.sext, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]
          repeat' split
          all_goals
            simp_all [RuntimeValue.isRefinedBy, isRefinedBy]
            try grind
end Veir.InstSimplify
