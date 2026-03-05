import Veir.Pass
import Veir.PatternRewriter.Basic

namespace Veir

/-!
  #Instcombine pass

  This file contains a (very) partial implementation of the instcombine pass, which performs
  simple peephole optimizations on the IR, such as folding constants or simplifying arithmetic.
-/

/-! ## Some helper functions for matching -/

/--
  Match an operation that has a single result, a specific opcode,
  and a specific number of operands.
  Returns the operands and the properties of the operation if it matches, or `none` otherwise.
-/
def matchOp (op : OperationPtr) (ctx : IRContext OpCode) (opType : OpCode) (numOperands : Nat) :
    Option (Array ValuePtr × propertiesOf opType) := do
  guard (op.getOpType! ctx = opType)
  guard (op.getNumOperands! ctx = numOperands)
  guard (op.getNumResults! ctx = 1)
  let operands := op.getOperands! ctx
  some (operands, op.getProperties! ctx opType)

def matchAddi (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf .llvm_add) := do
  let (op, properties) ← matchOp op ctx .llvm_add 2
  return (op[0]!, op[1]!, properties)

def matchMuli (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf .llvm_mul) := do
  let (op, properties) ← matchOp op ctx .llvm_mul 2
  return (op[0]!, op[1]!, properties)

def matchConstantOp (op : OperationPtr) (ctx : IRContext OpCode) : Option IntegerAttr := do
  let .llvm_constant := op.getOpType! ctx | none
  let properties := op.getProperties! ctx .llvm_constant
  return properties.value

def matchConstantVal (val : ValuePtr) (ctx : IRContext OpCode) : Option IntegerAttr := do
  let .opResult opResultPtr := val | none
  let op := opResultPtr.op
  matchConstantOp op ctx

/-! ## Pattern Rewrites -/

set_option warn.sorry false in
/-- Rewrites `x * 2` to `x + x`. -/
def mulITwoToAddi (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, properties) := matchMuli op rewriter.ctx
    | return rewriter
  let some cst := matchConstantVal rhs rewriter.ctx
    | return rewriter
  if cst.value ≠ 2 then
    return rewriter
  let (rewriter, newOp) ← rewriter.createOp .llvm_add #[lhs.getType! rewriter.ctx] #[lhs, lhs]
    #[] #[] properties (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry

set_option warn.sorry false in
/-- Rewrites `x * 0` to `0`. -/
def mulIZeroToCst (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, properties) := matchMuli op rewriter.ctx
    | return rewriter
  let some cst := matchConstantVal rhs rewriter.ctx
    | return rewriter
  if cst.value ≠ 0 then
    return rewriter
  let .integerType type := (lhs.getType! rewriter.ctx).val
    | return rewriter
  let cstProp := LLVMConstantProperties.mk (IntegerAttr.mk 0 type)
  let (rewriter, newOp) ← rewriter.createOp .llvm_constant #[lhs.getType! rewriter.ctx] #[]
    #[] #[] cstProp (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry

set_option warn.sorry false in
def InstCombinePass.impl (ctx : { ctx' : IRContext OpCode // ctx'.WellFormed }) (op : OperationPtr)
    (_ : op.InBounds ctx.val) :
    ExceptT String IO { ctx' : IRContext OpCode // ctx'.WellFormed } := do
  let pattern := RewritePattern.GreddyRewritePattern #[mulITwoToAddi, mulIZeroToCst]
  match RewritePattern.applyInContext pattern ctx ctx.property.inBounds with
  | none => throw "Error while applying pattern rewrites"
  | some ctx => pure ⟨ctx, sorry⟩

public def InstCombinePass : Pass OpCode :=
  { name := "instcombine"
    description :=
      "Combine instructions into more efficient forms, e.g., fold constants or simplify llvmmetic."
    run := InstCombinePass.impl }
