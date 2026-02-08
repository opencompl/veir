import Veir.PatternRewriter.Basic

namespace Veir

structure PatState where
  pw : PatternRewriter
  ip : InsertPoint

abbrev PatRewM := ExceptT Unit (StateM PatState)

inductive ArithOp where
| CstOp (n w : UInt64)
| AddiOp (x y : ValuePtr) (w : UInt64)
| SubiOp (x y : ValuePtr) (w : UInt64)

def ArithOp.getOpType : ArithOp → Nat
| .CstOp _ _ => 1
| .AddiOp _ _ _ => 2
| .SubiOp _ _ _ => 6
def ArithOp.getType : ArithOp → Array TypeAttr
| .CstOp _ w | .AddiOp _ _ w | .SubiOp _ _ w => #[s!"i{w}"]
def ArithOp.getOperands : ArithOp → Array ValuePtr
| .CstOp _ _ => #[]
| .AddiOp x y _ | .SubiOp x y _ => #[x, y]
def ArithOp.getProp : ArithOp → UInt64
| .CstOp n _ => n
| _ => 0

def OperationPtr.getOpType! (op : OperationPtr) : PatRewM Nat := do
  let s ← MonadState.get
  return (op.get! s.pw.ctx).opType

def OperationPtr.getOperandM! (op : OperationPtr) (n : Nat) : PatRewM ValuePtr := do
  let s ← MonadState.get
  return op.getOperand! s.pw.ctx n

def OperationPtr.getLhs! (op : OperationPtr) : PatRewM ValuePtr :=
  op.getOperandM! 0

def OperationPtr.getRhs! (op : OperationPtr) : PatRewM ValuePtr :=
  op.getOperandM! 1

def insertOp! (op : ArithOp) : PatRewM OperationPtr := do
  let s ← MonadState.get
  let ctx := s.pw.ctx
  let some (ctx, op) := Rewriter.createOp ctx op.getOpType op.getType op.getOperands
      #[] #[] op.getProp s.ip sorry sorry sorry sorry s.pw.ctx_fib
    | throw ()
  set { s with pw := {s.pw with ctx, ctx_fib := by sorry} }
  return op

def replaceOp! (op₁ op₂ : OperationPtr) : PatRewM Unit := do
  let s ← MonadState.get
  let ctx := s.pw.ctx
  let some ctx := Rewriter.replaceOp? ctx op₁ op₂ sorry sorry sorry sorry
  set { s with pw := {s.pw with ctx, ctx_fib := by sorry} }



def SubSelf (op : OperationPtr) : PatRewM Unit := do
  if (← op.getOpType!) ≠ 6 /- opType of subi -/ then return
  if (← op.getLhs!) ≠ (← op.getRhs!) then
    return
  let zero ← insertOp! (.CstOp 0 32)
  replaceOp! op zero
