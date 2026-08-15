module

public import Veir.Passes.Matching.Basic
public import Veir.Dialects.LLVM.OpInfo

public section

/-! This file contains helper functions to match operations when defining a rewrite. -/

namespace Veir

variable {OpCode : Type} [HasOpInfo OpCode] [HasDialect OpCode Llvm]

def matchAddi (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × propertiesOf Llvm.add) := do
  let (op, properties) ← matchOp op ctx (Llvm.add) 2
  return (op[0]!, op[1]!, properties)

def matchAdd (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × propertiesOf Llvm.add) := do
  let (op, properties) ← matchOp op ctx (Llvm.add) 2
  return (op[0]!, op[1]!, properties)

def matchSubi (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × propertiesOf Llvm.sub) := do
  let (op, properties) ← matchOp op ctx (Llvm.sub) 2
  return (op[0]!, op[1]!, properties)

def matchMuli (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × propertiesOf Llvm.mul) := do
  let (op, properties) ← matchOp op ctx (Llvm.mul) 2
  return (op[0]!, op[1]!, properties)

def matchAndi (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr) := do
  let (op, _) ← matchOp op ctx (Llvm.and) 2
  return (op[0]!, op[1]!)

def matchAnd (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × propertiesOf Llvm.and) := do
  let (op, properties) ← matchOp op ctx (Llvm.and) 2
  return (op[0]!, op[1]!, properties)

def matchOri (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × propertiesOf Llvm.or) := do
  let (op, properties) ← matchOp op ctx (Llvm.or) 2
  return (op[0]!, op[1]!, properties)

def matchXori (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr) := do
  let (op, _) ← matchOp op ctx (Llvm.xor) 2
  return (op[0]!, op[1]!)

def matchConstantIntOp (op : OperationPtr) (ctx : IRContext OpCode) :
    Option IntegerAttr := do
  let Llvm.mlir__constant := toDialect? Llvm (op.getOpType! ctx) | none
  let properties := op.getProperties! ctx Llvm.mlir__constant
  let .integer intAttr := properties.value | none
  return intAttr

def matchConstantIntVal (val : ValuePtr) (ctx : IRContext OpCode) :
    Option IntegerAttr := do
  let .opResult opResultPtr := val | none
  let op := opResultPtr.op
  matchConstantIntOp op ctx

/-- Match a constant integer with value zero, returning `val` itself. -/
def matchConstantZero (val : ValuePtr) (ctx : IRContext OpCode) : Option ValuePtr := do
  let attr ← matchConstantIntVal val ctx
  guard (attr.value = 0)
  return val

def matchAshr (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × propertiesOf Llvm.ashr) := do
  let (op, properties) ← matchOp op ctx (Llvm.ashr) 2
  return (op[0]!, op[1]!, properties)

def matchIcmp (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × propertiesOf Llvm.icmp) := do
  let (op, properties) ← matchOp op ctx (Llvm.icmp) 2
  return (op[0]!, op[1]!, properties)

def matchOr (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × propertiesOf Llvm.or) := do
  let (op, properties) ← matchOp op ctx (Llvm.or) 2
  return (op[0]!, op[1]!, properties)

/-- Match `llvm.select cond, tval, fval`, returning `(cond, tval, fval)`. -/
def matchSelect (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × ValuePtr) := do
  let (op, _) ← matchOp op ctx (Llvm.select) 3
  return (op[0]!, op[1]!, op[2]!)

def matchXor (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × propertiesOf Llvm.xor) := do
  let (op, properties) ← matchOp op ctx (Llvm.xor) 2
  return (op[0]!, op[1]!, properties)

def matchSmax (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr) := do
  let (op, _) ← matchOp op ctx (Llvm.intr__smax) 2
  return (op[0]!, op[1]!)

def matchSmin (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr) := do
  let (op, _) ← matchOp op ctx (Llvm.intr__smin) 2
  return (op[0]!, op[1]!)

def matchUmax (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr) := do
  let (op, _) ← matchOp op ctx (Llvm.intr__umax) 2
  return (op[0]!, op[1]!)

def matchUmin (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr) := do
  let (op, _) ← matchOp op ctx (Llvm.intr__umin) 2
  return (op[0]!, op[1]!)

/-- Match `llvm.intr.abs`, returning its single value operand. The
    `is_int_min_poison` flag is an attribute, not an operand, and does not affect
    the RISC-V lowering, so it is ignored here. -/
def matchAbs (op : OperationPtr) (ctx : IRContext OpCode) : Option ValuePtr := do
  let (op, _) ← matchOp op ctx (Llvm.intr__abs) 1
  return op[0]!

def matchSaddSat (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr) := do
  let (op, _) ← matchOp op ctx (Llvm.intr__sadd__sat) 2
  return (op[0]!, op[1]!)

def matchUaddSat (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr) := do
  let (op, _) ← matchOp op ctx (Llvm.intr__uadd__sat) 2
  return (op[0]!, op[1]!)

def matchSsubSat (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr) := do
  let (op, _) ← matchOp op ctx (Llvm.intr__ssub__sat) 2
  return (op[0]!, op[1]!)

def matchUsubSat (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr) := do
  let (op, _) ← matchOp op ctx (Llvm.intr__usub__sat) 2
  return (op[0]!, op[1]!)

def matchSshlSat (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr) := do
  let (op, _) ← matchOp op ctx (Llvm.intr__sshl__sat) 2
  return (op[0]!, op[1]!)

def matchUshlSat (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr) := do
  let (op, _) ← matchOp op ctx (Llvm.intr__ushl__sat) 2
  return (op[0]!, op[1]!)

/-- Match `llvm.intr.fshl`, returning the two data operands and the shift amount. -/
def matchFshl (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × ValuePtr) := do
  let (op, _) ← matchOp op ctx (Llvm.intr__fshl) 3
  return (op[0]!, op[1]!, op[2]!)

/-- Match `llvm.intr.fshr`, returning the two data operands and the shift amount. -/
def matchFshr (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × ValuePtr) := do
  let (op, _) ← matchOp op ctx (Llvm.intr__fshr) 3
  return (op[0]!, op[1]!, op[2]!)

/-- Match `xor X, -1` (the canonical "not X"), returning `X`. -/
def matchNot (val : ValuePtr) (ctx : IRContext OpCode) : Option ValuePtr := do
  let .opResult opResultPtr := val | none
  let op := opResultPtr.op
  let (lhs, rhs) ← matchXori op ctx
  let cst ← matchConstantIntVal rhs ctx
  guard (cst.value = -1)
  return lhs

def matchMul (op : OperationPtr) (ctx : IRContext OpCode) :
Option (ValuePtr × ValuePtr × propertiesOf Llvm.mul) := do
  let (op, properties) ← matchOp op ctx (Llvm.mul) 2
  return (op[0]!, op[1]!, properties)

def matchSdiv (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × propertiesOf Llvm.sdiv) := do
  let (op, properties) ← matchOp op ctx (Llvm.sdiv) 2
  return (op[0]!, op[1]!, properties)

def matchUdiv (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × propertiesOf Llvm.udiv) := do
  let (op, properties) ← matchOp op ctx (Llvm.udiv) 2
  return (op[0]!, op[1]!, properties)

def matchSrem (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × propertiesOf Llvm.srem) := do
  let (op, properties) ← matchOp op ctx (Llvm.srem) 2
  return (op[0]!, op[1]!, properties)

def matchUrem (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × propertiesOf Llvm.urem) := do
  let (op, properties) ← matchOp op ctx (Llvm.urem) 2
  return (op[0]!, op[1]!, properties)

def matchSext (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × propertiesOf Llvm.sext) := do
  let (op, properties) ← matchOp op ctx (Llvm.sext) 1
  return (op[0]!, properties)

def matchTrunc (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × propertiesOf Llvm.trunc) := do
  let (op, properties) ← matchOp op ctx (Llvm.trunc) 1
  return (op[0]!, properties)

def matchZext (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × propertiesOf Llvm.zext) := do
  let (op, properties) ← matchOp op ctx (Llvm.zext) 1
  return (op[0]!, properties)

def matchShl (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × propertiesOf Llvm.shl) := do
  let (op, properties) ← matchOp op ctx (Llvm.shl) 2
  return (op[0]!, op[1]!, properties)

def matchLshr (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × propertiesOf Llvm.lshr) := do
  let (op, properties) ← matchOp op ctx (Llvm.lshr) 2
  return (op[0]!, op[1]!, properties)

def matchSub (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × propertiesOf Llvm.sub) := do
  let (op, properties) ← matchOp op ctx (Llvm.sub) 2
  return (op[0]!, op[1]!, properties)

def matchBitcast (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × propertiesOf Llvm.bitcast) := do
  let (op, properties) ← matchOp op ctx (Llvm.bitcast) 1
  return (op[0]!, properties)

def matchLoad (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × propertiesOf Llvm.load) := do
  let (op, properties) ← matchOp op ctx (Llvm.load) 1
  return (op[0]!, properties)

def matchCtlz (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × propertiesOf Llvm.intr__ctlz) := do
  let (op, properties) ← matchOp op ctx (Llvm.intr__ctlz) 1
  return (op[0]!, properties)

def matchCttz (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × propertiesOf Llvm.intr__cttz) := do
  let (op, properties) ← matchOp op ctx (Llvm.intr__cttz) 1
  return (op[0]!, properties)

def matchCtpop (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × propertiesOf Llvm.intr__ctpop) := do
  let (op, properties) ← matchOp op ctx (Llvm.intr__ctpop) 1
  return (op[0]!, properties)

def matchBswap (op : OperationPtr) (ctx : IRContext OpCode) : Option ValuePtr := do
  let (op, _) ← matchOp op ctx (Llvm.intr__bswap) 1
  return op[0]!

def matchBitreverse (op : OperationPtr) (ctx : IRContext OpCode) : Option ValuePtr := do
  let (op, _) ← matchOp op ctx (Llvm.intr__bitreverse) 1
  return op[0]!

/--
  Match a `llvm.getelementptr` with a single dynamic index.
-/
def matchGetelementptr (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × propertiesOf Llvm.getelementptr) := do
  let (op, properties) ← matchOp op ctx (Llvm.getelementptr) 2
  return (op[0]!, op[1]!, properties)

def matchPoison (op : OperationPtr) (ctx : IRContext OpCode) : Option Unit := do
  let (_, _) ← matchOp op ctx (Llvm.mlir__poison) 0
  return ()

def matchStore (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × propertiesOf Llvm.store) := do
  guard (op.getOpType! ctx = Llvm.store)
  guard (op.getNumOperands! ctx = 2)
  let operands := op.getOperands! ctx
  let properties := op.getProperties! ctx Llvm.store
  return (operands[0]!, operands[1]!, properties)

def matchFreeze (op : OperationPtr) (ctx : IRContext OpCode) : Option ValuePtr := do
  let (op, _) ← matchOp op ctx (Llvm.freeze) 1
  return (op[0]!)
