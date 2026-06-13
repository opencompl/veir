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

def matchAnd (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr) := do
  let (op, _) ← matchOp op ctx (.llvm .and) 2
  return (op[0]!, op[1]!)

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

def matchXor (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.llvm .xor)) := do
  let (op, properties) ← matchOp op ctx (.llvm .xor) 2
  return (op[0]!, op[1]!, properties)

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

/--
  Match a `llvm.getelementptr` with a single dynamic index.
-/
def matchGetelementptr (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × propertiesOf (.llvm .getelementptr)) := do
  let (op, properties) ← matchOp op ctx (.llvm .getelementptr) 2
  return (op[0]!, op[1]!, properties)

def matchStore (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × propertiesOf (.llvm .store)) := do
  guard (op.getOpType! ctx = .llvm .store)
  guard (op.getNumOperands! ctx = 2)
  let operands := op.getOperands! ctx
  let properties := op.getProperties! ctx (.llvm .store)
  return (operands[0]!, operands[1]!, properties)

/-! ## Facts derived from a successful `matchOp` -/

/-- A successful `matchOp` implies the matched operation has exactly one result. -/
theorem matchOp_getNumResults {op : OperationPtr} {ctx : IRContext OpCode} {opType : OpCode}
    {n : Nat} {res : Array ValuePtr × propertiesOf opType}
    (h : matchOp op ctx opType n = some res) : op.getNumResults! ctx = 1 := by
  unfold matchOp guard at h
  simp only [bind, Option.bind, pure, failure] at h
  grind

/-- A successful `matchOp` implies the matched operation has `n` operands. -/
theorem matchOp_getNumOperands {op : OperationPtr} {ctx : IRContext OpCode} {opType : OpCode}
    {n : Nat} {res : Array ValuePtr × propertiesOf opType}
    (h : matchOp op ctx opType n = some res) : op.getNumOperands! ctx = n := by
  unfold matchOp guard at h
  simp only [bind, Option.bind, pure, failure] at h
  grind

/-- The operand array returned by `matchOp` is the operation's operand list. -/
theorem matchOp_operands {op : OperationPtr} {ctx : IRContext OpCode} {opType : OpCode}
    {n : Nat} {ops : Array ValuePtr} {props : propertiesOf opType}
    (h : matchOp op ctx opType n = some (ops, props)) : ops = op.getOperands! ctx := by
  unfold matchOp guard at h
  simp only [bind, Option.bind, pure, failure] at h
  grind

/-- A successful `matchOp` with a positive operand count implies the op is in bounds:
    an out-of-bounds operation reads as the default, which has no operands. -/
theorem matchOp_inBounds {op : OperationPtr} {ctx : IRContext OpCode} {opType : OpCode}
    {n : Nat} {res : Array ValuePtr × propertiesOf opType}
    (hpos : 0 < n) (h : matchOp op ctx opType n = some res) : op.InBounds ctx := by
  have hn := matchOp_getNumOperands h
  by_cases hin : op.InBounds ctx
  · exact hin
  · exfalso
    grind [OperationPtr.getNumOperands!, OperationPtr.get!_of_not_inBounds,
      Operation.default_operands_eq]
