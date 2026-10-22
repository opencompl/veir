import Veir.InstSimplify.IntrinsicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
/-- Nested min/max constant ordering, with both commutations and earlier saturation branches excluded. -/
def IS7102 (kind : MinMaxKind) (c1 c2 : Int) (si so : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x ← MatchProg.value ty
    let a ← matchBitConstant ty c1
    let inner ← MatchProg.operation (.llvm kind.op) (match si with | true => #[a,x] | false => #[x,a]) #[ty]
    -- Upstream tests the first inner constant before the second.
    let _ : Unit ← MatchProg.inspectOperation inner.op (fun ctx op => do
      if !si then
        if let some defop := (op.getOperand! ctx 0).definingOp? then
          guard (defop.getOpType! ctx != .llvm .mlir__constant)
      pure ())
    let b ← matchBitConstant ty c2
    MatchProg.matchNative ty (fun t => match t.val with
      | .integerType t =>
        let a := BitVec.ofInt t.bitwidth c1
        let b := BitVec.ofInt t.bitwidth c2
        kind.nonStrictPred.eval a b && !(b == kind.saturation t.bitwidth) && !(b == kind.inverse.saturation t.bitwidth)
      | _ => false)
    let _ ← MatchProg.root (.llvm kind.op) (match so with | true => #[b,inner.res[0]!] | false => #[inner.res[0]!,b]) #[ty]
    return inner.res[0]!)
  pure (fun x => x)
theorem IS7102_valid (kind : MinMaxKind) (c1 c2 : Int) (si so : Bool) : Pattern.Valid (IS7102 kind c1 c2 si so) := by
  cases kind <;> cases si <;> cases so
  all_goals
    simp only [IS7102, MinMaxKind.op, matchBitConstant]
    provePuddleValid
    rintro ⟨w,s⟩
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x
    rintro ap av ai ip iv ii bp bv bi rp rv ri ha _ hb hg
    obtain rfl := matched_bit_constant_eq _ _ _ _ ai ha
    obtain rfl := matched_bit_constant_eq _ _ _ _ bi hb
    first
    | obtain rfl := (smax_iff _ _ _ _ _).mp ii
    | obtain rfl := (smin_iff _ _ _ _ _).mp ii
    | obtain rfl := (umax_iff _ _ _ _ _).mp ii
    | obtain rfl := (umin_iff _ _ _ _ _).mp ii
    first
    | obtain rfl := (smax_iff _ _ _ _ _).mp ri
    | obtain rfl := (smin_iff _ _ _ _ _).mp ri
    | obtain rfl := (umax_iff _ _ _ _ _).mp ri
    | obtain rfl := (umin_iff _ _ _ _ _).mp ri
    simp [TypeAttr.of_val, Attribute.of, -Attribute.integerType_eq_of, MinMaxKind.nonStrictPred, LLVM.IntPred.eval, Bool.and_eq_true, Bool.not_eq_true, -BitVec.toInt_ofInt, -BitVec.toNat_ofInt] at hg
    rcases hg with ⟨⟨horder,hsat⟩,hinv⟩
    cases x with
    | poison => simp [LLVM.Int.smax, LLVM.Int.smin, LLVM.Int.umax, LLVM.Int.umin, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
    | val x =>
      simp only [LLVM.Int.smax, LLVM.Int.smin, LLVM.Int.umax, LLVM.Int.umin, Id.run, pure]
      repeat' split
      all_goals
        simp_all [RuntimeValue.isRefinedBy, isRefinedBy, BitVec.sle, BitVec.ule, MinMaxKind.nonStrictPred, LLVM.IntPred.eval, -BitVec.toInt_ofInt, -BitVec.toNat_ofInt]
        all_goals first
        | apply BitVec.eq_of_toInt_eq
          omega
        | apply BitVec.eq_of_toNat_eq
          omega
        | omega
end Veir.InstSimplify
