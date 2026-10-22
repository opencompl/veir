import Veir.InstSimplify.MiscSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

theorem signextend_truncate_bits {w n : Nat} (x : BitVec w) (hw : w ≤ n) :
    (x.signExtend n).truncate w = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  by_cases hi : i < w
  · simp [BitVec.getLsbD_signExtend, BitVec.getElem_signExtend, hi, show i < n by omega]
  · simp [BitVec.getLsbD_of_ge, Nat.le_of_not_gt hi]

def IS5693_extend_trunc (signed : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let src ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let mid ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    MatchProg.matchNative (src,mid) (fun (w,n) => match w.val,n.val with
      | .integerType w,.integerType n => w.bitwidth < n.bitwidth
      | _,_ => false)
    let x ← MatchProg.value src
    let e ← MatchProg.operation (.llvm (match signed with | true => Llvm.sext | false => .zext)) #[x] #[mid]
    let _ ← MatchProg.root (.llvm .trunc) e.res #[src]
    return x)
  pure (fun x => x)
theorem IS5693_extend_trunc_valid (signed : Bool) : Pattern.Valid (IS5693_extend_trunc signed) := by
  cases signed
  all_goals
    simp only [IS5693_extend_trunc]
    provePuddleValid
    rintro ⟨w,s⟩ ⟨n,ns⟩
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x
    rintro ep ev ei rp rv ri hw
    have hw : w < n := by simpa [TypeAttr.of_val, Attribute.of, -Attribute.integerType_eq_of] using hw
    first
    | obtain rfl := (misc_zext_iff ⟨w,s⟩ ⟨n,ns⟩ _ _ _ hw).mp ei
    | obtain rfl := (sext_iff ⟨w,s⟩ ⟨n,ns⟩ _ _ _ hw).mp ei
    obtain rfl := (misc_trunc_iff ⟨n,ns⟩ ⟨w,s⟩ _ _ _ hw).mp ri
    cases x with
    | poison => simp [LLVM.Int.zext, LLVM.Int.sext, LLVM.Int.trunc, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
    | val x =>
      simp only [LLVM.Int.zext, LLVM.Int.sext, LLVM.Int.trunc, Id.run, pure]
      repeat' split
      all_goals
        simp_all [RuntimeValue.isRefinedBy, isRefinedBy, signextend_truncate_bits x (Nat.le_of_lt hw),
          BitVec.truncate, BitVec.zeroExtend, BitVec.setWidth_setWidth_of_le x (Nat.le_of_lt hw)]
        try grind


def IS5693_bitcast_int : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let mid ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    MatchProg.matchNative (ty,mid) (fun (a,b) => match a.val,b.val with
      | .integerType a,.integerType b => a.bitwidth == b.bitwidth
      | _,_ => false)
    let x ← MatchProg.value ty
    let i ← MatchProg.operation (.llvm .bitcast) #[x] #[mid]
    let _ ← MatchProg.root (.llvm .bitcast) i.res #[ty]
    return x)
  pure (fun x => x)
theorem IS5693_bitcast_int_valid : Pattern.Valid IS5693_bitcast_int := by
  simp only [IS5693_bitcast_int]
  provePuddleValid
  rintro ⟨w,s⟩ ⟨n,ns⟩
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro x ip iv ii rp rv ri hn
  have hn : w = n := by simpa [TypeAttr.of_val,Attribute.of,-Attribute.integerType_eq_of] using hn
  subst n
  obtain rfl := misc_bitcast_int_eq ⟨w,ns⟩ _ _ _ ii
  obtain rfl := misc_bitcast_int_eq _ _ _ _ ri
  exact RuntimeValue.isRefinedBy_refl _

def IS5693_bitcast_ptr : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := LLVM.PointerType) (fun _ => true)
    let x ← MatchProg.value ty
    let i ← MatchProg.operation (.llvm .bitcast) #[x] #[ty]
    let _ ← MatchProg.root (.llvm .bitcast) i.res #[ty]
    return x)
  pure (fun x => x)
theorem IS5693_bitcast_ptr_valid : Pattern.Valid IS5693_bitcast_ptr := by
  simp only [IS5693_bitcast_ptr]
  provePuddleValid
  rintro ⟨⟩
  simp only [RuntimeValue.Conforms.llvmPointerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro x ip iv ii rp rv ri
  obtain rfl := misc_bitcast_ptr_eq _ _ _ ii
  obtain rfl := misc_bitcast_ptr_eq _ _ _ ri
  exact RuntimeValue.isRefinedBy_refl _


/-- Same-type identity in VeIR's additional byte representation. -/
def IS5693_bitcast_byte : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := LLVM.ByteType) (fun _ => true)
    let x ← MatchProg.value ty
    let i ← MatchProg.operation (.llvm .bitcast) #[x] #[ty]
    let _ ← MatchProg.root (.llvm .bitcast) i.res #[ty]
    return x) pure (fun x => x)
theorem IS5693_bitcast_byte_valid : Pattern.Valid IS5693_bitcast_byte := by
  simp only [IS5693_bitcast_byte]
  provePuddleValid
  rintro ⟨w⟩
  simp only [RuntimeValue.Conforms.byteType,forall_exists_index,forall_eq_apply_imp_iff]
  rintro x ip iv ii rp rv ri
  have he := ii.2 MemoryState.empty
  simp only [interpretOp', Llvm.interpretOp', TypeAttr.of_def, Attribute.of_def, IsAttr.inject] at he
  simp at he
  obtain rfl : iv = .byte w x := by simpa using he.symm
  have he := ri.2 MemoryState.empty
  simp only [interpretOp', Llvm.interpretOp', TypeAttr.of_def, Attribute.of_def, IsAttr.inject] at he
  simp at he
  obtain rfl : rv = .byte w x := by simpa using he.symm
  exact RuntimeValue.isRefinedBy_refl _
end Veir.InstSimplify
