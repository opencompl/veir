import Veir.Pass
import Veir.PatternRewriter.Basic

/-! This file contains helper functions to match operations when defining a rewrite. -/

namespace Veir

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

def matchAddi (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.llvm .add)) := do
  let (op, properties) ← matchOp op ctx (.llvm .add) 2
  return (op[0]!, op[1]!, properties)

def matchAdd (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.llvm .add)) := do
  let (op, properties) ← matchOp op ctx (.llvm .add) 2
  return (op[0]!, op[1]!, properties)

def matchSubi (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.llvm .sub)) := do
  let (op, properties) ← matchOp op ctx (.llvm .sub) 2
  return (op[0]!, op[1]!, properties)

def matchMuli (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.llvm .mul)) := do
  let (op, properties) ← matchOp op ctx (.llvm .mul) 2
  return (op[0]!, op[1]!, properties)

def matchAndi (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr) := do
  let (op, _) ← matchOp op ctx (.llvm .and) 2
  return (op[0]!, op[1]!)

def matchAnd (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.llvm .and)) := do
  let (op, properties) ← matchOp op ctx (.llvm .and) 2
  return (op[0]!, op[1]!, properties)

def matchOri (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.llvm .or)) := do
  let (op, properties) ← matchOp op ctx (.llvm .or) 2
  return (op[0]!, op[1]!, properties)

def matchXori (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr) := do
  let (op, _) ← matchOp op ctx (.llvm .xor) 2
  return (op[0]!, op[1]!)

def matchConstantIntOp (op : OperationPtr) (ctx : IRContext OpCode) : Option IntegerAttr := do
  let .llvm .mlir__constant := op.getOpType! ctx | none
  let properties := op.getProperties! ctx (.llvm .mlir__constant)
  let .integer intAttr := properties.value | none
  return intAttr

def matchConstantIntVal (val : ValuePtr) (ctx : IRContext OpCode) : Option IntegerAttr := do
  let .opResult opResultPtr := val | none
  let op := opResultPtr.op
  matchConstantIntOp op ctx

/-- Match a constant integer with value zero, returning `val` itself. -/
def matchConstantZero (val : ValuePtr) (ctx : IRContext OpCode) : Option ValuePtr := do
  let attr ← matchConstantIntVal val ctx
  guard (attr.value = 0)
  return val

/--
  Return the operation that defines `val`, if `val` is the result of an operation
  (rather than a block argument). Used for matching multi-operation patterns.
-/
def getDefiningOp (val : ValuePtr) (_ctx : IRContext OpCode) : Option OperationPtr := do
  let .opResult opResultPtr := val | none
  some opResultPtr.op

def matchCastOp (op : OperationPtr) (ctx : IRContext OpCode) : Option IntegerAttr := do
  let .builtin .unrealized_conversion_cast := op.getOpType! ctx | none
  let properties := op.getProperties! ctx (.llvm .mlir__constant)
  let .integer intAttr := properties.value | none
  return intAttr

def matchAshr (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.llvm .ashr)) := do
  let (op, properties) ← matchOp op ctx (.llvm .ashr) 2
  return (op[0]!, op[1]!, properties)

def matchIcmp (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.llvm .icmp)) := do
  let (op, properties) ← matchOp op ctx (.llvm .icmp) 2
  return (op[0]!, op[1]!, properties)

def matchOr (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.llvm .or)) := do
  let (op, properties) ← matchOp op ctx (.llvm .or) 2
  return (op[0]!, op[1]!, properties)

/-- Match `llvm.select cond, tval, fval`, returning `(cond, tval, fval)`. -/
def matchSelect (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × ValuePtr) := do
  let (op, _) ← matchOp op ctx (.llvm .select) 3
  return (op[0]!, op[1]!, op[2]!)

def matchXor (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.llvm .xor)) := do
  let (op, properties) ← matchOp op ctx (.llvm .xor) 2
  return (op[0]!, op[1]!, properties)

def matchSmax (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr) := do
  let (op, _) ← matchOp op ctx (.llvm .intr__smax) 2
  return (op[0]!, op[1]!)

def matchSmin (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr) := do
  let (op, _) ← matchOp op ctx (.llvm .intr__smin) 2
  return (op[0]!, op[1]!)

def matchUmax (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr) := do
  let (op, _) ← matchOp op ctx (.llvm .intr__umax) 2
  return (op[0]!, op[1]!)

def matchUmin (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr) := do
  let (op, _) ← matchOp op ctx (.llvm .intr__umin) 2
  return (op[0]!, op[1]!)

/-- Match `llvm.intr.fshl`, returning the two data operands and the shift amount. -/
def matchFshl (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × ValuePtr) := do
  let (op, _) ← matchOp op ctx (.llvm .intr__fshl) 3
  return (op[0]!, op[1]!, op[2]!)

/-- Match `llvm.intr.fshr`, returning the two data operands and the shift amount. -/
def matchFshr (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × ValuePtr) := do
  let (op, _) ← matchOp op ctx (.llvm .intr__fshr) 3
  return (op[0]!, op[1]!, op[2]!)

/-- Match `xor X, -1` (the canonical "not X"), returning `X`. -/
def matchNot (val : ValuePtr) (ctx : IRContext OpCode) : Option ValuePtr := do
  let .opResult opResultPtr := val | none
  let op := opResultPtr.op
  let (lhs, rhs) ← matchXori op ctx
  let cst ← matchConstantIntVal rhs ctx
  guard (cst.value = -1)
  return lhs

def matchMul (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.llvm .mul)) := do
  let (op, properties) ← matchOp op ctx (.llvm .mul) 2
  return (op[0]!, op[1]!, properties)

def matchSdiv (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.llvm .sdiv)) := do
  let (op, properties) ← matchOp op ctx (.llvm .sdiv) 2
  return (op[0]!, op[1]!, properties)

def matchUdiv (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.llvm .udiv)) := do
  let (op, properties) ← matchOp op ctx (.llvm .udiv) 2
  return (op[0]!, op[1]!, properties)

def matchSrem (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.llvm .srem)) := do
  let (op, properties) ← matchOp op ctx (.llvm .srem) 2
  return (op[0]!, op[1]!, properties)

def matchUrem (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.llvm .urem)) := do
  let (op, properties) ← matchOp op ctx (.llvm .urem) 2
  return (op[0]!, op[1]!, properties)

def matchSext (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.llvm .sext)) := do
  let (op, properties) ← matchOp op ctx (.llvm .sext) 1
  return (op[0]!, properties)

def matchTrunc (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.llvm .trunc)) := do
  let (op, properties) ← matchOp op ctx (.llvm .trunc) 1
  return (op[0]!, properties)

def matchZext (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.llvm .zext)) := do
  let (op, properties) ← matchOp op ctx (.llvm .zext) 1
  return (op[0]!, properties)

def matchShl (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.llvm .shl)) := do
  let (op, properties) ← matchOp op ctx (.llvm .shl) 2
  return (op[0]!, op[1]!, properties)

def matchLshr (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.llvm .lshr)) := do
  let (op, properties) ← matchOp op ctx (.llvm .lshr) 2
  return (op[0]!, op[1]!, properties)

def matchSub (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.llvm .sub)) := do
  let (op, properties) ← matchOp op ctx (.llvm .sub) 2
  return (op[0]!, op[1]!, properties)

def matchLoad (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.llvm .load)) := do
  let (op, properties) ← matchOp op ctx (.llvm .load) 1
  return (op[0]!, properties)

def matchCtlz (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × propertiesOf (.llvm .intr__ctlz)) := do
  let (op, properties) ← matchOp op ctx (.llvm .intr__ctlz) 1
  return (op[0]!, properties)

def matchCttz (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × propertiesOf (.llvm .intr__cttz)) := do
  let (op, properties) ← matchOp op ctx (.llvm .intr__cttz) 1
  return (op[0]!, properties)

def matchCtpop (op : OperationPtr) (ctx : IRContext OpCode) : Option ValuePtr := do
  let (op, _) ← matchOp op ctx (.llvm .intr__ctpop) 1
  return op[0]!

def matchBswap (op : OperationPtr) (ctx : IRContext OpCode) : Option ValuePtr := do
  let (op, _) ← matchOp op ctx (.llvm .intr__bswap) 1
  return op[0]!

def matchBitreverse (op : OperationPtr) (ctx : IRContext OpCode) : Option ValuePtr := do
  let (op, _) ← matchOp op ctx (.llvm .intr__bitreverse) 1
  return op[0]!

/--
  Match a `llvm.getelementptr` with a single dynamic index.
-/
def matchGetelementptr (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × propertiesOf (.llvm .getelementptr)) := do
  let (op, properties) ← matchOp op ctx (.llvm .getelementptr) 2
  return (op[0]!, op[1]!, properties)

def matchPoison (op : OperationPtr) (ctx : IRContext OpCode) : Option Unit := do
  let (_, _) ← matchOp op ctx (.llvm .mlir__poison) 0
  return ()

def matchStore (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × propertiesOf (.llvm .store)) := do
  guard (op.getOpType! ctx = .llvm .store)
  guard (op.getNumOperands! ctx = 2)
  let operands := op.getOperands! ctx
  let properties := op.getProperties! ctx (.llvm .store)
  return (operands[0]!, operands[1]!, properties)
