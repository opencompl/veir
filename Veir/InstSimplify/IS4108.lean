import Veir.InstSimplify.CmpCastSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
/-- An out-of-range literal compared with scalar sext; the native guard is exact truncate/re-extend inequality. -/
def IS4108 (constant : Int) : Pattern OpCode := Pattern.Builder
  (do
    let src ← MatchProg.type (Attr := IntegerType)
    let dst ← MatchProg.type (Attr := IntegerType)
    let cty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let x ← MatchProg.value src
    let c ← matchIntConstant dst constant
    let extended ← MatchProg.operation (.llvm .sext) #[x] #[dst]
    let _ ← MatchProg.root (.llvm .icmp) #[extended.res[0]!,c] #[cty] (fun p => p.predicate == .sgt || p.predicate == .sge)
    MatchProg.matchNative (src,dst) (fun (s,d) => castNonroundtripGuard true constant s d)
    return (dst,cty))
  (fun (dst,cty) => do
    let p ← CreateProg.applyNative dst (fun t => match t.val with
      | .integerType it => some (LLVMConstantProperties.mk (.integer (IntegerAttr.mk
          (CastCompareLiteral.value .negative constant it.bitwidth) (IntegerType.signless 1))))
      | _ => none)
    CreateProg.operation (.llvm .mlir__constant) #[] #[cty] p)
  (fun x => x)

theorem IS4108_valid (constant : Int) : Pattern.Valid (IS4108 constant) := by
  simp only [IS4108, matchIntConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ ⟨v,ds⟩ _ ⟨cw,cs⟩ rfl hcw x cp cv ch ci ep ev ei ip iv ih ii hg
  have : cw = 1 := by simpa using hcw
  subst cw
  have hg : 0 < w ∧ ((BitVec.ofInt v constant).setWidth w).signExtend v ≠ BitVec.ofInt v constant := by
    simpa [castNonroundtripGuard, TypeAttr.of_val, Attribute.of, -Attribute.integerType_eq_of] using hg
  obtain rfl := (matched_constant_iff _ _ _ ch _).mp ci
  have hw := sext_width_lt ⟨w,s⟩ ⟨v,ds⟩ _ _ _ ei
  change w < v at hw
  obtain rfl := (sext_iff ⟨w,s⟩ ⟨v,ds⟩ _ _ _ hw).mp ei
  obtain rfl := (icmp_iff _ _ _ _ _).mp ii
  refine ⟨_, (constant_iff _ _ _ rfl _).mpr rfl, ?_⟩
  clear ci ei ii
  cases x with
  | poison => simp [LLVM.Int.sext, LLVM.Int.icmp, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
  | val x =>
    simp only [LLVM.Int.sext, Id.run, pure]
    have hord := sext_nonroundtrip_order x (BitVec.ofInt v constant) hw hg.1 hg.2
    have hpwide : ip.predicate = .eq ∨ ip.predicate = .ne ∨ ip.predicate = .sgt ∨ ip.predicate = .sge ∨ ip.predicate = .slt ∨ ip.predicate = .sle := by
      try simp only [Bool.or_eq_true, beq_iff_eq] at ih
      grind
    rw [icmp_signed_outside _ _ hord ip.predicate hpwide]
    rcases ip with ⟨pred⟩
    cases pred <;> (try simp at ih) <;>
      simp [unsignedCmpResult, outsideCmpResult, CastCompareLiteral.value,
        RuntimeValue.isRefinedBy, isRefinedBy, bool_bit_integer]
end Veir.InstSimplify
