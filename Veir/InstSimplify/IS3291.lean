import Veir.InstSimplify.CmpSelectSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
/-- Unsigned/equality scalar remainder-bound cases; signed cases require value analysis certificates. -/
def IS3291 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let cty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let x ← MatchProg.value ty
    let y ← MatchProg.value ty
    let rem ← MatchProg.operation (.llvm .urem) #[x,y] #[ty]
    let _ ← MatchProg.root (.llvm .icmp) #[rem.res[0]!,y] #[cty] (fun p => p.predicate == .ne || p.predicate == .ult || p.predicate == .ule)
    return cty)
  (fun ty => do
    let p ← CreateProg.property (.llvm .mlir__constant)
      (LLVMConstantProperties.mk (.integer (IntegerAttr.mk 1 (IntegerType.signless 1))))
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
  (fun x => x)

theorem IS3291_valid : Pattern.Valid IS3291 := by
  simp only [IS3291]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ _ ⟨cw,cs⟩ rfl hw x y rp rv ri ip iv ih ii
  have : cw = 1 := by simpa using hw
  subst cw
  obtain ⟨hu,rfl⟩ := (urem_iff _ _ _ _ _).mp ri
  obtain rfl := (icmp_iff _ _ _ _ _).mp ii
  refine ⟨.int 1 (.val (BitVec.ofInt 1 1)), ?_, ?_⟩
  · exact (constant_iff _ _ _ rfl _).mpr rfl
  · cases y with
    | poison => simp [LLVM.Int.isUnsignedDivisionUB] at hu
    | val y =>
      have hy : y ≠ 0 := by simpa [LLVM.Int.isUnsignedDivisionUB] using hu
      have hyn : y.toNat ≠ 0 := by
        intro hz
        apply hy
        apply BitVec.eq_of_toNat_eq
        simpa using hz
      cases x with
      | poison => simp [LLVM.Int.urem, LLVM.Int.icmp, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
      | val x =>
        have hb := Nat.mod_lt x.toNat (Nat.pos_of_ne_zero hyn)
        rcases ip with ⟨pred⟩
        cases pred <;>
          simp_all [LLVM.Int.urem, LLVM.Int.icmp, LLVM.IntPred.eval, BitVec.ofNat_eq_ofNat,
            BitVec.ult, BitVec.ule, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]
        all_goals simp_all [← BitVec.toNat_inj, BitVec.toNat_umod]
        all_goals omega
end Veir.InstSimplify
