import Veir.Pass
import Veir.Rewriter.WfRewriter
import Veir.Data.LLVM.Int.Basic

/-!
  # Local common subexpression elimination

  This pass implements a small, conservative CSE:
  * it only reasons within one basic block;
  * it only considers arithmetic operations (including icmps, select,
    and ext/trunc);
  * it only works for instructions that return a single result;
  * distinct UB flags are treated as distinct instructions;
  * it only supports the LLVM dialect (arith would be trivial to add);
  * it does not use a worklist or iterate to fixpoint, so it may leave
    work undone when it finishes.
-/

namespace Veir
namespace CSE

/-- Here we package up an opcode with its UB flags; we don't want to
   mix up, e.g., "add" and "add nsw". -/
abbrev Kind := (op : OpCode) × propertiesOf op

instance : Hashable Kind where
  hash k := mixHash (hash k.fst) (hash k.snd)

/-- This is the basis for CSE: if two instructions have the same Key,
    then they compute the same value: they are interchangeable. In
    that case we can remove one of them and switch all of its uses to
    the other. Proving this will be the crux of the eventual
    correctness proof for this pass. -/
structure Key where
  kind : Kind
  resultType : TypeAttr
  operands : Array ValuePtr
deriving DecidableEq, BEq, Hashable

def makeKey
    (ctx : IRContext OpCode) (op : OperationPtr) (kind : Kind)
    (operands : Array ValuePtr) :
    Key :=
  {
    kind
    resultType := (op.getResult 0 : ValuePtr).getType! ctx
    operands
  }

/-- Because ValuePtr is a sum type where the numeric IDs assigned to
    an opResult and a blockArgument might overlap, we add a separate
    tag to discriminate them reliably for purposes of computing a
    total order -/
def valueSortKey (value : ValuePtr) : Nat × Nat × Nat :=
  match value with
  | .opResult result => (0, result.op.id, result.index)
  | .blockArgument arg => (1, arg.block.id, arg.index)

/-- Given two ValuePtrs (that are operands to a commutative binop),
    return them in a canonical order so that we can CSE the binop
    regardless of the order in which its operands happen to be
    specified -/
def binaryOperandsCanonicalOrder (lhs rhs : ValuePtr) : ValuePtr × ValuePtr :=
  let (lhsTag, lhsID, lhsIndex) := valueSortKey lhs
  let (rhsTag, rhsID, rhsIndex) := valueSortKey rhs
  if lhsTag < rhsTag ||
      (lhsTag = rhsTag && (lhsID < rhsID || (lhsID = rhsID && lhsIndex ≤ rhsIndex))) then
    (lhs, rhs)
  else
    (rhs, lhs)

def commutativeBinopKey (ctx : IRContext OpCode) (op : OperationPtr)
    (kind : Kind) : Key :=
  let lhs := op.getOperand! ctx 0
  let rhs := op.getOperand! ctx 1
  let (lhs, rhs) := binaryOperandsCanonicalOrder lhs rhs
  makeKey ctx op kind #[lhs, rhs]

def ordinaryKey
    (ctx : IRContext OpCode) (op : OperationPtr) (kind : Kind) :
    Key :=
  makeKey ctx op kind (op.getOperands! ctx)

/-- Compute the Key for an `llvm.icmp`, canonicalizing equivalent
    predicate/operand pairs. So, for example, `sgt x y` becomes
    `slt y x`. -/
def icmpKey
    (ctx : IRContext OpCode) (op : OperationPtr)
    (props : propertiesOf (.llvm .icmp)) :
    Key :=
  let kind : Kind := ⟨.llvm .icmp, props⟩
  let lhs := op.getOperand! ctx 0
  let rhs := op.getOperand! ctx 1
  let swappedKey (pred : Data.LLVM.IntPred) : Key :=
    let props := { props with predicate := pred }
    makeKey ctx op ⟨.llvm .icmp, props⟩ #[rhs, lhs]
  match props.predicate with
  | .eq | .ne => commutativeBinopKey ctx op kind
  | .slt | .sle | .ult | .ule => ordinaryKey ctx op kind
  | .sgt => swappedKey .slt
  | .sge => swappedKey .sle
  | .ugt => swappedKey .ult
  | .uge => swappedKey .ule

/-- Return op's Key if it is supported by this pass, otherwise return
    None. -/
def key? (ctx : IRContext OpCode) (op : OperationPtr) : Option Key := do
  guard ((op.get! ctx).attrs.entries.size = 0)
  guard (op.getNumResults! ctx = 1)
  let opType := op.getOpType! ctx
  let properties := op.getProperties! ctx opType
  let kind : Kind := ⟨opType, properties⟩
  match opType with
  | .llvm .add | .llvm .mul | .llvm .and | .llvm .or | .llvm .xor
  | .llvm .intr__smax | .llvm .intr__smin | .llvm .intr__umax | .llvm .intr__umin =>
      return commutativeBinopKey ctx op kind
  | .llvm .icmp =>
      return icmpKey ctx op (op.getProperties! ctx (.llvm .icmp))
  | .llvm .sub | .llvm .mlir__constant
  | .llvm .shl | .llvm .lshr | .llvm .ashr
  | .llvm .sdiv | .llvm .udiv | .llvm .srem | .llvm .urem
  | .llvm .zext | .llvm .sext | .llvm .trunc
  | .llvm .select =>
      return ordinaryKey ctx op kind
  | _ => none

set_option warn.sorry false in
/-- Perform CSE on a single BB: Walk the operations, building up a
    hash of available values. For any operation whose value is already
    available, replace it with the earlier one. -/
def processBlock
    (ctx : WfIRContext OpCode) (block : BlockPtr) :
    WfIRContext OpCode := Id.run do
  let mut ctx := ctx
  let mut available : Std.HashMap Key OperationPtr := Std.HashMap.emptyWithCapacity
  let mut current := (block.get! ctx.raw).firstOp
  while current.isSome do
    let op := current.get!
    let next := (op.get! ctx.raw).next
    if let some key := key? ctx.raw op then
        match available[key]? with
        | some earlier =>
            ctx := WfRewriter.replaceValue ctx (op.getResult 0) (earlier.getResult 0) sorry sorry sorry
            ctx := WfRewriter.eraseOp ctx op sorry sorry sorry
        | none =>
            available := available.insert key op
    current := next
  return ctx

set_option warn.sorry false in
def processAllBlocks (ctx : WfIRContext OpCode) :
    WfIRContext OpCode := Id.run do
  let mut ctx := ctx
  for block in ctx.raw.blocks.keys do
    ctx := processBlock ctx block
  return ctx

def CSEPass.impl (ctx : WfIRContext OpCode) (_op : OperationPtr) (_ : _op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  pure (CSE.processAllBlocks ctx)

end CSE

public def CSEPass : Pass OpCode :=
  { name := "cse"
    description := "Eliminate common pure integer SSA expressions within each basic block."
    run := CSE.CSEPass.impl }

end Veir
