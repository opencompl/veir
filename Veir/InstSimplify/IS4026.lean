import Veir.InstSimplify.CmpCastSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
/-- An out-of-range literal compared with scalar zext; the native guard is exact truncate/re-extend inequality. -/
def IS4026 (constant : Int) : Pattern OpCode := Pattern.Builder
  (do
    let src ← MatchProg.type (Attr := IntegerType)
    let dst ← MatchProg.type (Attr := IntegerType)
    let cty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let x ← MatchProg.value src
    let c ← matchIntConstant dst constant
    let extended ← MatchProg.operation (.llvm .zext) #[x] #[dst]
    let _ ← MatchProg.root (.llvm .icmp) #[extended.res[0]!,c] #[cty] (fun p => p.predicate == .eq || p.predicate == .ugt || p.predicate == .uge)
    MatchProg.matchNative (src,dst) (fun (s,d) => castNonroundtripGuard false constant s d)
    return (dst,cty))
  (fun (dst,cty) => do
    let p ← CreateProg.applyNative dst (fun t => match t.val with
      | .integerType it => some (LLVMConstantProperties.mk (.integer (IntegerAttr.mk
          (CastCompareLiteral.value .falseValue constant it.bitwidth) (IntegerType.signless 1))))
      | _ => none)
    CreateProg.operation (.llvm .mlir__constant) #[] #[cty] p)
  (fun x => x)

theorem IS4026_valid (constant : Int) : Pattern.Valid (IS4026 constant) := by
  simp only [IS4026, matchIntConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ ⟨v,ds⟩ _ ⟨cw,cs⟩ rfl hcw x cp cv ch ci ep ev ei ip iv ih ii hg
  have : cw = 1 := by simpa using hcw
  subst cw
  have hg : 0 < w ∧ ((BitVec.ofInt v constant).setWidth w).zeroExtend v ≠ BitVec.ofInt v constant := by
    simpa [castNonroundtripGuard, TypeAttr.of_val, Attribute.of, -Attribute.integerType_eq_of] using hg
  obtain rfl := (matched_constant_iff _ _ _ ch _).mp ci
  have hw := logic_zext_width_lt ⟨w,s⟩ ⟨v,ds⟩ _ _ _ ei
  change w < v at hw
  obtain rfl := (logic_zext_iff ⟨w,s⟩ ⟨v,ds⟩ _ _ _ hw).mp ei
  obtain rfl := (icmp_iff _ _ _ _ _).mp ii
  refine ⟨_, (constant_iff _ _ _ rfl _).mpr rfl, ?_⟩
  clear ci ei ii
  cases x with
  | poison => simp [LLVM.Int.zext, LLVM.Int.icmp, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
  | val x =>
    rcases logic_zext_outcomes x v ep.nneg hw with hz | hz
    · simp [hz, LLVM.Int.icmp, Id.run, RuntimeValue.isRefinedBy, isRefinedBy]
    · rw [hz]
      have hlt := zext_nonroundtrip_lt x (BitVec.ofInt v constant) hw hg.2
      have hord := zext_nonroundtrip_order x (BitVec.ofInt v constant) hw hg.2
      have hpwide : ip.predicate = .eq ∨ ip.predicate = .ne ∨ ip.predicate = .ugt ∨ ip.predicate = .uge ∨ ip.predicate = .ult ∨ ip.predicate = .ule := by
        try simp only [Bool.or_eq_true, beq_iff_eq] at ih
        grind
      rw [icmp_unsigned_lt _ _ hlt ip.predicate hpwide]
      rcases ip with ⟨pred⟩
      cases pred <;> (try simp at ih) <;>
        simp [unsignedCmpResult, outsideCmpResult, CastCompareLiteral.value,
          RuntimeValue.isRefinedBy, isRefinedBy, bool_bit_integer]
end Veir.InstSimplify
