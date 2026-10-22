import Veir.InstSimplify.CmpSelectSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
/-- The scalar self-comparison part of the rule; LLVM undef is outside the runtime domain. -/
def IS3918 (pred : LLVM.IntPred) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let cty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let x ← MatchProg.value ty
    let _ ← MatchProg.root (.llvm .icmp) #[x,x] #[cty] (fun p => p.predicate == pred)
    return cty)
  (fun ty => do
    let p ← CreateProg.property (.llvm .mlir__constant)
      (LLVMConstantProperties.mk (.integer (IntegerAttr.mk
        (if pred == .eq || pred == .uge || pred == .ule || pred == .sge || pred == .sle then 1 else 0)
        (IntegerType.signless 1))))
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
  (fun x => x)

theorem IS3918_valid (pred : LLVM.IntPred) : Pattern.Valid (IS3918 pred) := by
  simp only [IS3918]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ _ ⟨cw,cs⟩ rfl hw x ip iv ih ii
  have : cw = 1 := by simpa using hw
  subst cw
  obtain rfl := (icmp_iff _ _ _ _ _).mp ii
  have hp : ip.predicate = pred := by simpa using ih
  refine ⟨.int 1 (.val (BitVec.ofInt 1 (if pred == .eq || pred == .uge || pred == .ule || pred == .sge || pred == .sle then 1 else 0))), ?_, ?_⟩
  · exact (constant_iff _ _ _ rfl _).mpr rfl
  · cases x <;> cases pred <;> simp [LLVM.Int.icmp, LLVM.IntPred.eval, BitVec.ult, BitVec.ule, BitVec.slt, BitVec.sle, hp, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]
end Veir.InstSimplify
