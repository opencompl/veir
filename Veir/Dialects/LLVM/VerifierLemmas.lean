module
public import Veir.Verifier
import all Veir.Verifier
import all Veir.Verifier.Basic
import all Veir.Dialects.LLVM.OpInfo
import all Veir.IR.Attribute
import all Veir.IR.Basic
import all Veir.GlobalOpInfo
import all Veir.IR.OpCode
public section

namespace Veir
/-- The integer constant verifier checks equality of the full attribute and result types. -/
theorem OperationPtr.Verified.llvm_mlir__constant_integer_type {ctx : WfIRContext OpCode} {op : OperationPtr} {opInBounds}
    {intAttr : IntegerAttr}
    (opVerify : op.Verified ctx opInBounds)
    (opType : op.getOpType! ctx.raw = .llvm .mlir__constant)
    (hProp : (op.getProperties! ctx.raw Llvm.mlir__constant).value = .integer intAttr) :
    ((op.getResult 0).getType! ctx.raw).val = Attribute.of IntegerType intAttr.type := by
  obtain ⟨intTy, hType⟩ := opVerify.llvm_mlir__constant_resultType opType hProp
  rw [OperationPtr.Verified] at opVerify
  simp only [OperationPtr.verifyLocalInvariants, HasOpInfo.verifyLocalInvariants,
    OpCode.verifyLocalInvariants, Llvm.verifyLocalInvariants,
    ← OperationPtr.getOpType!_eq_getOpType, opType] at opVerify
  replace opVerify := Except.ok_of_bind_ok opVerify
  simp only [hProp, hType, Attribute.of_def, IsAttr.inject] at opVerify
  simp only [bind, Except.bind] at opVerify
  split at opVerify
  · cases opVerify
  · rename_i h
    split at opVerify
    · cases opVerify
    · rename_i h
      simp only [ne_eq, Decidable.not_not] at h
      exact h ▸ hType
/-- The type equality from an integer constant's verifier, in the form used by Puddle. -/
theorem IsFromVerifiedOp.llvm_constant_type {t : IntegerType} {a : IntegerAttr}
    {p : LLVMConstantProperties}
    (h : IsFromVerifiedOp (.llvm .mlir__constant) #[] #[.of IntegerType t] p)
    (hp : p.value = .integer a) : a.type = t := by
  obtain ⟨ctx, op, hin, hv, hop, _, htypes, hprops⟩ := h
  have hprop : (op.getProperties! ctx.raw Llvm.mlir__constant).value = .integer a := by
    have heq : op.getProperties! ctx.raw Llvm.mlir__constant =
        op.getProperties! ctx.raw (OpCode.llvm .mlir__constant) := by
      have hop' : (op.get! ctx.raw).opType = OpCode.llvm .mlir__constant := by
        simpa [OperationPtr.getOpType!] using hop
      simp [OperationPtr.getProperties!, hop', ofDialect, HasDialect.toDialectProperties, HasDialect.inject]
    rw [heq, hprops]
    exact hp
  have ht := hv.llvm_mlir__constant_integer_type hop hprop
  have hr : (op.getResult 0).getType! ctx.raw = .of IntegerType t := by
    have hn : 0 < (op.getResultTypes! ctx.raw).size := by simp [htypes]
    have he := OperationPtr.getResultTypes!.getElem_eq (ctx := ctx.raw) (op := op) (h := hn)
    simpa [htypes] using he.symm
  rw [hr] at ht
  simpa only [TypeAttr.of_def, Attribute.of_def, IsAttr.inject, Attribute.integerType.injEq] using ht.symm
/-- Normalize an integer constant match without losing its verifier hypothesis. -/
theorem forall_verified_integer_constant {t : IntegerType} {G P : IntegerAttr → Prop} :
    (∀ a, G a → IsFromVerifiedOp (.llvm .mlir__constant) #[] #[.of IntegerType t]
        { value := .integer a } → P a) ↔
    ∀ v, G ⟨v, t⟩ → IsFromVerifiedOp (.llvm .mlir__constant) #[] #[.of IntegerType t]
        { value := .integer ⟨v, t⟩ } → P ⟨v, t⟩ := by
  constructor
  · exact fun h v => h ⟨v, t⟩
  · intro h a hg hv
    have ht := hv.llvm_constant_type rfl
    cases a with
    | mk v ty => cases ht; exact h v hg hv

end Veir
