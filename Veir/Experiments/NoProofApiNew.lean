import Veir.PatternRewriter.Basic
import Veir.Properties

namespace Veir

structure PatState where
  pw : PatternRewriter OpCode
  ip : InsertPoint

abbrev PatRewM := ExceptT Unit (StateM PatState)

def OperationPtr.getOpTypeM! (op : OperationPtr) : PatRewM OpCode := do
  let s ← MonadState.get
  return (op.get! s.pw.ctx).opType

def OperationPtr.getOperandM! (op : OperationPtr) (n : Nat) : PatRewM ValuePtr := do
  let s ← MonadState.get
  return op.getOperand! s.pw.ctx n

def OperationPtr.getLhs! (op : OperationPtr) : PatRewM ValuePtr :=
  op.getOperandM! 0

def OperationPtr.getRhs! (op : OperationPtr) : PatRewM ValuePtr :=
  op.getOperandM! 1

def createOp! (opCode : OpCode) (properties : propertiesOf opCode)
  (resultTypes : Array TypeAttr) (operands : Array ValuePtr): PatRewM OperationPtr := do
  let s ← MonadState.get
  let ctx := s.pw.ctx
  let some (ctx, op) := Rewriter.createOp ctx opCode resultTypes operands
      #[] #[] properties s.ip sorry sorry sorry sorry s.pw.ctx_fib
    | throw ()
  set { s with pw := {s.pw with ctx, ctx_fib := by sorry} }
  return op

def replaceOp! (op₁ op₂ : OperationPtr) : PatRewM Unit := do
  let s ← MonadState.get
  let ctx := s.pw.ctx
  let some ctx := Rewriter.replaceOp? (OpInfo := OpCode) ctx op₁ op₂ sorry sorry sorry sorry
  set { s with pw := {s.pw with ctx, ctx_fib := by sorry} }

def ArithConstantProperties.from (value : Int) (bitwidth : Nat) : ArithConstantProperties :=
  ArithConstantProperties.mk (IntegerAttr.mk value (IntegerType.mk bitwidth))

def SubSelf (op : OperationPtr) : PatRewM Unit := do
  if (← op.getOpTypeM!) ≠ .arith_subi /- opType of subi -/ then return
  if (← op.getLhs!) ≠ (← op.getRhs!) then
    return
  let zero ← createOp! .arith_constant (ArithConstantProperties.from 0 32) #[IntegerType.mk 32] #[]
  replaceOp! op zero
