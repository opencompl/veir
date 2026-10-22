import Veir.InstSimplify.CmpSelectSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
/-- Arbitrary-width zero comparison. matchEquivZeroRHS has no other inputs producing this predicate. -/
def IS3076 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let cty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let x ← MatchProg.value ty
    let z ← matchIntConstant ty 0
    let _ ← MatchProg.root (.llvm .icmp) #[x,z] #[cty] (fun p => p.predicate == .uge)
    return cty)
  (fun ty => do
    let p ← CreateProg.property (.llvm .mlir__constant)
      (LLVMConstantProperties.mk (.integer (IntegerAttr.mk 1 (IntegerType.signless 1))))
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
  (fun x => x)

theorem IS3076_valid : Pattern.Valid IS3076 := by
  simp only [IS3076, matchIntConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ _ ⟨cw,cs⟩ rfl hw x zp zv zh zi ip iv ih ii
  have : cw = 1 := by simpa using hw
  subst cw
  obtain rfl := (matched_constant_iff _ _ _ zh _).mp zi
  obtain rfl := (icmp_iff _ _ _ _ _).mp ii
  have hp : ip.predicate = .uge := by simpa using ih
  refine ⟨.int 1 (.val (BitVec.ofInt 1 1)), ?_, ?_⟩
  · exact (constant_iff _ _ _ rfl _).mpr rfl
  · cases x <;> simp [LLVM.Int.icmp, LLVM.IntPred.eval, BitVec.ult, BitVec.ule, BitVec.slt, BitVec.sle, hp, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]
end Veir.InstSimplify
