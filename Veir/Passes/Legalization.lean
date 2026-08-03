module

public import Veir.Pass
import Veir.Passes.Matching

/-!
  This pass legalizes LLVM operations to prepare for instruction selection.
  For now, this is restricted to widening integer values.
-/

namespace Veir

/--
  Sigma type for an operation plus its properties.
-/
abbrev OpWithProp := (op : OpCode) × (HasOpInfo.propertiesOf op)

/--
  Converts the types of the arguments and result of a single-result binary operation.
-/
def convertBinaryOp (ctx : WfIRContext OpCode) (op : OperationPtr) (newtype : TypeAttr) (convLhs convRhs newOp convRes : OpWithProp) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let type := ((op.getResult 0).get! ctx.raw).type
  let [lhs, rhs] := (op.getOperands! ctx.raw).toList | return (ctx, none)
  let (ctx, lhsOp) ← WfRewriter.createOp! ctx convLhs.fst #[newtype] #[lhs] #[] #[] convLhs.snd none
  let (ctx, rhsOp) ← WfRewriter.createOp! ctx convRhs.fst #[newtype] #[rhs] #[] #[] convRhs.snd none
  let (ctx, newOp) ← WfRewriter.createOp! ctx newOp.fst #[newtype] #[lhsOp.getResult 0, rhsOp.getResult 0] #[] #[] newOp.snd none
  let (ctx, resOp) ← WfRewriter.createOp! ctx convRes.fst #[type] #[newOp.getResult 0] #[] #[] convRes.snd none
  return (ctx, some (#[lhsOp, rhsOp, newOp, resOp], #[resOp.getResult 0]))

/--
  Integer values can be zero-extended, sign-extended, or any-extended (i.e., extended with arbitrary bits).
-/
inductive IntegerExtKind
| any
| zero
| sign

/--
  Return the LLVM operation corresponding to an `IntegerExtKind`.
-/
def expandIntegerExtOp (type : IntegerExtKind) : ((op : OpCode) × HasOpInfo.propertiesOf op) :=
  match type with
  | .sign => .mk (OpCode.llvm .sext) ()
  | .zero => .mk (OpCode.llvm .zext) (.mk false)
  | .any => .mk (OpCode.llvm .zext) (.mk false) -- FIXME

/--
  Widen the operands and result type of a homogeneously-typed binary LLVM operation.
-/
def widenSimpleBinaryIntOp (ctx : WfIRContext OpCode) (op : OperationPtr) (newBw : Nat) (extType : IntegerExtKind) (newOp : Option OpWithProp := none) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let oldOp := Sigma.mk (op.getOpType! ctx.raw) (op.getProperties! ctx.raw (op.getOpType! ctx.raw))
  let .integerType ⟨bw⟩ := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if bw ≥ newBw then return (ctx, none)
  let expandOp := expandIntegerExtOp extType
  convertBinaryOp ctx op (IntegerType.mk newBw) expandOp expandOp (newOp.getD oldOp) ⟨.llvm .trunc, .mk false false⟩

/--
  Widen the operands and result type of an LLVM operation.
-/
-- TODO incomplete
def widenOperations (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  match op.getOpType! ctx.raw with
  | .llvm .add =>
    widenSimpleBinaryIntOp ctx op 64 .any (some ⟨.llvm .add, .mk false false⟩)
  | .llvm .sub =>
    widenSimpleBinaryIntOp ctx op 64 .any (some ⟨.llvm .sub, .mk false false⟩)
  | .llvm .mul =>
    widenSimpleBinaryIntOp ctx op 64 .any (some ⟨.llvm .mul, .mk false false⟩)
  | .llvm .and =>
    widenSimpleBinaryIntOp ctx op 64 .any (some ⟨.llvm .and, ()⟩)
  | .llvm .xor =>
    widenSimpleBinaryIntOp ctx op 64 .any (some ⟨.llvm .xor, ()⟩)
  | .llvm .or =>
    widenSimpleBinaryIntOp ctx op 64 .any (some ⟨.llvm .or, .mk false⟩)
  | _ => return (ctx, none)

def LegalizePass.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  match RewritePattern.applyInContext (RewritePattern.GreedyRewritePattern #[.fromLocalRewrite widenOperations]) ctx with
  | none => throw "Error while applying legalization"
  | some ctx => pure ctx

public def LegalizePass : Pass OpCode :=
  { name := "legalize"
    description := "Legalize types."
    run := LegalizePass.impl }
