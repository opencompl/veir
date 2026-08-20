module

public import Veir.Verifier.Basic
import all Veir.Verifier.Basic

namespace Veir

public section

variable {OpInfo : Type} [HasOpInfo OpInfo]

/--
  Structural facts shared by successful integer binary-operation checks.
-/
def OperationPtr.IsVerifiedIntegerBinop
    (op : OperationPtr) (ctx : WfIRContext OpInfo) : Prop :=
  op.getNumResults! ctx.raw = 1 ∧
  op.getNumOperands! ctx.raw = 2 ∧
  op.getNumSuccessors! ctx.raw = 0 ∧
  op.getNumRegions! ctx.raw = 0 ∧
  ∃ integerType,
    ((op.getResult 0).get! ctx.raw).type =
      Attribute.asType (.integerType integerType) (by grind) ∧
    ((op.getOperand! ctx.raw 0).getType! ctx.raw) =
      Attribute.asType (.integerType integerType) (by grind) ∧
    ((op.getOperand! ctx.raw 1).getType! ctx.raw) =
      Attribute.asType (.integerType integerType) (by grind)

/-- Extract structural facts from a successful `verifyIntegerBinop` check. -/
theorem OperationPtr.verifyIntegerBinop_eq_ok
    {ctx : WfIRContext OpInfo} {op : OperationPtr}
    {opInBounds : op.InBounds ctx.raw}
    (h : op.verifyIntegerBinop ctx opInBounds = .ok ()) :
    op.IsVerifiedIntegerBinop ctx := by
  simp only [IsVerifiedIntegerBinop, verifyIntegerBinop, verifyPlainOpCounts,
    verifyOperandTypesMatch, verifyResultTypeMatches, TypeAttr.verifyIntegerType, ne_eq, bind,
    Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at h ⊢
  simp only [TypeAttr.inj]
  grind

/--
  Structural facts shared by successful select-operation checks.
-/
def OperationPtr.IsVerifiedSelect
    (op : OperationPtr) (ctx : WfIRContext OpInfo) : Prop :=
  op.getNumResults! ctx.raw = 1 ∧
  op.getNumOperands! ctx.raw = 3 ∧
  (∃ it,
    ((op.getOperand! ctx.raw 0).getType! ctx.raw).val = .integerType it ∧
    it.bitwidth = 1) ∧
  ((op.getResult 0).get! ctx.raw).type.val =
    ((op.getOperand! ctx.raw 1).getType! ctx.raw).val ∧
  ((op.getResult 0).get! ctx.raw).type.val =
    ((op.getOperand! ctx.raw 2).getType! ctx.raw).val

/-- Extract structural facts from a successful `verifySelectTypes` check. -/
theorem OperationPtr.verifySelectTypes_eq_ok
    {ctx : WfIRContext OpInfo} {op : OperationPtr}
    {opInBounds : op.InBounds ctx.raw}
    (h : op.verifySelectTypes ctx opInBounds = .ok ()) :
    op.IsVerifiedSelect ctx := by
  simp only [IsVerifiedSelect] at ⊢
  simp [verifySelectTypes, verifyPlainOpCounts, verifyOperandTypesMatch,
    verifyResultTypeMatches, TypeAttr.verifyI1, bind, Except.bind, throw, throwThe,
    MonadExceptOf.throw, pure, Except.pure] at h
  grind [getNumOperands!_eq_getNumOperands, getNumResults!_eq_getNumResults]

/--
  Structural facts shared by successful integer unary-operation checks.
-/
def OperationPtr.IsVerifiedIntegerUnop
    (op : OperationPtr) (ctx : WfIRContext OpInfo) : Prop :=
  op.getNumResults! ctx.raw = 1 ∧
  op.getNumOperands! ctx.raw = 1 ∧
  op.getNumSuccessors! ctx.raw = 0 ∧
  op.getNumRegions! ctx.raw = 0 ∧
  ((op.getResult 0).get! ctx.raw).type =
    (op.getOperand! ctx.raw 0).getType! ctx.raw ∧
  ∃ integerType isT,
    ((op.getResult 0).get! ctx.raw).type = Attribute.asType (.integerType integerType) isT

/-- Extract structural facts from a successful `verifyIntegerUnop` check. -/
theorem OperationPtr.verifyIntegerUnop_eq_ok
    {ctx : WfIRContext OpInfo} {op : OperationPtr}
    {opInBounds : op.InBounds ctx.raw} {ty}
    (h : op.verifyIntegerUnop ctx opInBounds = .ok ty) :
    op.IsVerifiedIntegerUnop ctx := by
  simp only [IsVerifiedIntegerUnop, verifyIntegerUnop, verifyPlainOpCounts,
    verifyResultTypeMatches, TypeAttr.verifyIntegerType, ne_eq, bind, Except.bind, throw,
    throwThe, MonadExceptOf.throw, pure, Except.pure] at h ⊢
  simp only [TypeAttr.inj]
  split at h <;> grind

/--
  Structural facts shared by successful integer ternary-operation checks.
-/
def OperationPtr.IsVerifiedIntegerTernop
    (op : OperationPtr) (ctx : WfIRContext OpInfo) : Prop :=
  op.getNumResults! ctx.raw = 1 ∧
  op.getNumOperands! ctx.raw = 3 ∧
  op.getNumSuccessors! ctx.raw = 0 ∧
  op.getNumRegions! ctx.raw = 0 ∧
  ∃ integerType,
    ((op.getResult 0).get! ctx.raw).type =
      Attribute.asType (.integerType integerType) (by grind) ∧
    ((op.getOperand! ctx.raw 0).getType! ctx.raw) =
      Attribute.asType (.integerType integerType) (by grind) ∧
    ((op.getOperand! ctx.raw 1).getType! ctx.raw) =
      Attribute.asType (.integerType integerType) (by grind) ∧
    ((op.getOperand! ctx.raw 2).getType! ctx.raw) =
      Attribute.asType (.integerType integerType) (by grind)

/-- Extract structural facts from a successful `verifyIntegerTernop` check. -/
theorem OperationPtr.verifyIntegerTernop_eq_ok
    {ctx : WfIRContext OpInfo} {op : OperationPtr}
    {opInBounds : op.InBounds ctx.raw}
    (h : op.verifyIntegerTernop ctx opInBounds = .ok ()) :
    op.IsVerifiedIntegerTernop ctx := by
  simp only [IsVerifiedIntegerTernop, verifyIntegerTernop, verifyPlainOpCounts,
    verifyOperandTypesMatch, verifyResultTypeMatches, TypeAttr.verifyIntegerType, ne_eq, bind,
    Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at h ⊢
  simp only [TypeAttr.inj]
  split at h <;> grind

/--
  Structural facts shared by successful integer extension-operation checks.
-/
def OperationPtr.IsVerifiedIntegerExtop
    (op : OperationPtr) (ctx : WfIRContext OpInfo) : Prop :=
  op.getNumResults! ctx.raw = 1 ∧
  op.getNumOperands! ctx.raw = 1 ∧
  op.getNumSuccessors! ctx.raw = 0 ∧
  op.getNumRegions! ctx.raw = 0 ∧
  ∃ operandType resultType,
    ((op.getOperand! ctx.raw 0).getType! ctx.raw) =
      Attribute.asType (.integerType operandType) (by grind) ∧
    ((op.getResult 0).get! ctx.raw).type =
      Attribute.asType (.integerType resultType) (by grind) ∧
    operandType.bitwidth < resultType.bitwidth

/-- Extract structural facts from a successful `verifyIntegerExtTypes` check. -/
theorem OperationPtr.verifyIntegerExtTypes_eq_ok
    {ctx : WfIRContext OpInfo} {op : OperationPtr}
    {opInBounds : op.InBounds ctx.raw}
    (h : op.verifyIntegerExtTypes ctx opInBounds = .ok ()) :
    op.IsVerifiedIntegerExtop ctx := by
  simp only [IsVerifiedIntegerExtop, verifyIntegerExtTypes, verifyPlainOpCounts, ne_eq, bind,
    Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at h ⊢
  simp only [TypeAttr.inj]
  split at h <;> grind

end

end Veir
