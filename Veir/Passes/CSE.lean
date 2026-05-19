import Veir.Pass
import Veir.PatternRewriter.Basic

namespace Veir

/-!
  # Local common subexpression elimination

  This pass implements a small, conservative CSE:
  * it only reasons within one basic block;
  * it only considers arithmetic operations;
  * distinct UB flags are treated as distinct instructions
  * it only supports the LLVM dialect (arith would be trivial to add)
  * it does not use a worklist or iterate to fixpoint, so it may leave
    work undone when it finishes
-/

abbrev CSEKind := (op : OpCode) × propertiesOf op

instance (opCode : OpCode) : DecidableEq (propertiesOf opCode) := by
  simp only [properties_of]
  cases opCode <;> (try simp) <;> (rename_i op; cases op <;> infer_instance)

instance : Hashable CSEKind where
  hash k := mixHash (hash k.fst) (hash k.snd)

structure CSEKey where
  kind : CSEKind
  resultType : TypeAttr
  operands : Array ValuePtr
deriving DecidableEq, BEq, Hashable

namespace CSE

def isIntegerType (type : TypeAttr) : Bool :=
  match type.val with
  | .integerType _ => true
  | _ => false

def valueSortKey (value : ValuePtr) : Nat × Nat × Nat :=
  match value with
  | .opResult result => (0, result.op.id, result.index)
  | .blockArgument arg => (1, arg.block.id, arg.index)

def lexNat3LE (lhs rhs : Nat × Nat × Nat) : Bool :=
  let (lhsTag, lhsID, lhsIndex) := lhs
  let (rhsTag, rhsID, rhsIndex) := rhs
  lhsTag < rhsTag ||
    (lhsTag = rhsTag && (lhsID < rhsID || (lhsID = rhsID && lhsIndex ≤ rhsIndex)))

def valueLE (lhs rhs : ValuePtr) : Bool :=
  lexNat3LE (valueSortKey lhs) (valueSortKey rhs)

def orderedBinaryOperands (lhs rhs : ValuePtr) : Array ValuePtr :=
  if valueLE lhs rhs then #[lhs, rhs] else #[rhs, lhs]

def allOperandsInteger (ctx : IRContext OpCode) (operands : Array ValuePtr) : Bool :=
  operands.all fun operand => isIntegerType (operand.getType! ctx)

def commutativeKey
    (ctx : IRContext OpCode) (op : OperationPtr) (kind : CSEKind) :
    Option CSEKey := do
  let operands := op.getOperands! ctx
  let lhs ← operands[0]?
  let rhs ← operands[1]?
  return {
    kind
    resultType := (op.getResult 0 : ValuePtr).getType! ctx
    operands := orderedBinaryOperands lhs rhs
  }

def ordinaryKey
    (ctx : IRContext OpCode) (op : OperationPtr) (kind : CSEKind) :
    CSEKey :=
  {
    kind
    resultType := (op.getResult 0 : ValuePtr).getType! ctx
    operands := op.getOperands! ctx
  }

def key? (ctx : IRContext OpCode) (op : OperationPtr) : Option CSEKey := do
  guard (op.getNumResults! ctx = 1)
  guard (op.getNumRegions! ctx = 0)
  guard ((op.get! ctx).attrs.entries.size = 0)
  let resultType := (op.getResult 0 : ValuePtr).getType! ctx
  guard (isIntegerType resultType)
  let operands := op.getOperands! ctx
  guard (allOperandsInteger ctx operands)
  let opType := op.getOpType! ctx
  let kind : CSEKind := ⟨opType, op.getProperties! ctx opType⟩
  match opType with
  | .llvm .mlir__constant =>
      return ordinaryKey ctx op kind
  | .llvm .add | .llvm .mul | .llvm .and | .llvm .or | .llvm .xor =>
      guard (operands.size = 2)
      commutativeKey ctx op kind
  | .llvm .sub | .llvm .icmp
  | .llvm .shl | .llvm .lshr | .llvm .ashr
  | .llvm .sdiv | .llvm .udiv | .llvm .srem | .llvm .urem =>
      guard (operands.size = 2)
      return ordinaryKey ctx op kind
  | .llvm .zext | .llvm .sext | .llvm .trunc =>
      guard (operands.size = 1)
      return ordinaryKey ctx op kind
  | .llvm .select =>
      guard (operands.size = 3)
      return ordinaryKey ctx op kind
  | _ => none

abbrev AvailableExprs := Std.HashMap CSEKey ValuePtr

set_option warn.sorry false in
def processBlock
    (rewriter : PatternRewriter OpCode) (block : BlockPtr) :
    Option (PatternRewriter OpCode) := do
  let mut rewriter := rewriter
  let mut available : AvailableExprs := Std.HashMap.emptyWithCapacity
  let mut current := (block.get! rewriter.ctx.raw).firstOp
  while current.isSome do
    let op := current.get!
    let next := (op.get! rewriter.ctx.raw).next
    match key? rewriter.ctx.raw op with
    | some key =>
        match available[key]? with
        | some earlier =>
            rewriter ← rewriter.replaceValue (op.getResult 0) earlier sorry sorry
            if !op.hasUses! rewriter.ctx.raw then
              rewriter ← rewriter.eraseOp op sorry sorry sorry
        | none =>
            available := available.insert key (op.getResult 0)
    | none => pure ()
    current := next
  return rewriter

set_option warn.sorry false in
def processAllBlocks (rewriter : PatternRewriter OpCode) :
    Option (PatternRewriter OpCode) := do
  let mut rewriter := rewriter
  for block in rewriter.ctx.raw.blocks.keys do
    if block.InBounds rewriter.ctx.raw then
      rewriter ← processBlock rewriter block
  return rewriter

end CSE

def CSEPass.impl (ctx : WfIRContext OpCode) (_op : OperationPtr) (_ : _op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  let rewriter : PatternRewriter OpCode := {
    ctx
    hasDoneAction := false
    worklist := PatternRewriter.Worklist.empty
  }
  match CSE.processAllBlocks rewriter with
  | none => throw "Error while applying CSE"
  | some rewriter => pure rewriter.ctx

public def CSEPass : Pass OpCode :=
  { name := "cse"
    description := "Eliminate common pure integer SSA expressions within each basic block."
    run := CSEPass.impl }

end Veir
