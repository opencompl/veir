module

public import Veir.Pass
import Veir.Rewriter.WfRewriter
import Veir.IR.Dominance

import Veir.Interfaces.SideEffectInterfaces

/-!
  # A simple common subexpression elimination pass:

  This pass implements a small, conservative CSE:
  * it reasons across basic blocks, using dominance;
  * it only considers memory-independent operations with no successors,
    regions, or extra attributes;
  * distinct UB flags are treated as distinct instructions;
  * it canonicalizes binary commutative operations and integer comparisons;
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
    then they compute the same ordered sequence of result values. If A
    and B have the same Key and A dominates B, then we can remove B and
    switch every result's uses to the corresponding result of A.
    Proving this will be the crux of the eventual correctness proof for
    this pass.

    `scope` is the nearest `IsolatedFromAbove` region enclosing the
    operation. It is part of the Key because rewiring B's uses to A's
    results makes those uses reference a value defined at A, which is
    only legal when no isolated boundary separates the two. -/
structure Key where
  kind : Kind
  resultTypes : Array TypeAttr
  operands : Array ValuePtr
  scope : Option RegionPtr
deriving DecidableEq, BEq, Hashable

def makeKey
    (ctx : IRContext OpCode) (op : OperationPtr) (kind : Kind)
    (operands : Array ValuePtr) :
    Key :=
  {
    kind
    resultTypes := op.getResultTypes! ctx
    operands
    scope := do (← op.getParentRegion! ctx).nearestIsolatedScope? ctx
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

/-- Compute the Key for an integer comparison (`llvm.icmp` or
    `arith.cmpi`), canonicalizing equivalent predicate/operand pairs.
    So, for example, `sgt x y` becomes `slt y x`. `mkKind` packages a
    predicate back up with the comparison's own opcode, so comparisons
    from different dialects never share a Key. -/
def icmpKey
    (ctx : IRContext OpCode) (op : OperationPtr)
    (mkKind : IcmpProperties → Kind) (props : IcmpProperties) :
    Key :=
  let kind : Kind := mkKind props
  let lhs := op.getOperand! ctx 0
  let rhs := op.getOperand! ctx 1
  let swappedKey (pred : Data.LLVM.IntPred) : Key :=
    makeKey ctx op (mkKind { props with predicate := pred }) #[rhs, lhs]
  match props.predicate with
  | .eq | .ne => commutativeBinopKey ctx op kind
  | .slt | .sle | .ult | .ule => ordinaryKey ctx op kind
  | .sgt => swappedKey .slt
  | .sge => swappedKey .sle
  | .ugt => swappedKey .ult
  | .uge => swappedKey .ule

/-- Return `op`'s key when it is eligible for CSE, otherwise return `none`. -/
def key? (ctx : IRContext OpCode) (op : OperationPtr) : Option Key := do
  guard (op.isMemoryIndependent ctx)
  guard (op.getNumSuccessors! ctx = 0)
  guard ((op.get! ctx).attrs.entries.size = 0)
  guard (op.getNumResults! ctx > 0)
  let opType := op.getOpType! ctx
  let properties := op.getProperties! ctx opType
  let kind : Kind := ⟨opType, properties⟩
  match opType with
  | .llvm .icmp =>
      return icmpKey ctx op (fun props => ⟨.llvm .icmp, props⟩)
        (op.getProperties! ctx Llvm.icmp)
  | .arith .cmpi =>
      return icmpKey ctx op (fun props => ⟨.arith .cmpi, props⟩)
        (op.getProperties! ctx Arith.cmpi)
  | _ =>
      if opType.isCommutative && op.getNumOperands! ctx = 2 then
        return commutativeBinopKey ctx op kind
      else
        return ordinaryKey ctx op kind

/-- Perform CSE: walk operations in dominance-friendly order, building
    up a single map of available values. Each key may have multiple
    candidates because the first equivalent operation we encounter may
    not dominate later equivalent operations in a different CFG
    branch. For any operation whose value is already available *and
    dominates it*, replace it with the earlier one. Candidates never
    cross an `IsolatedFromAbove` boundary, because the Key records the
    enclosing isolated scope. -/
def run (ctx : WfIRContext OpCode) (top : OperationPtr) :
    WfIRContext OpCode := Id.run do
  let some dfCtx := Veir.fixpointSolve top #[Veir.DominanceAnalysis] ctx
    | panic! "Dominance analysis not expected to fail"
  let ops := top.opsInDominanceOrder dfCtx ctx
  let mut ctx := ctx
  let mut available : Std.HashMap Key (Array OperationPtr) := Std.HashMap.emptyWithCapacity
  for op in ops do
    if _h : op.InBounds ctx.raw then
      if let some key := key? ctx.raw op then
        let candidates := available.getD key #[]
        match candidates.find? (·.properlyDominates op dfCtx ctx) with
        | some earlier =>
            ctx := WfRewriter.replaceOp! ctx op earlier
        | none =>
            available := available.insert key (candidates.push op)
  return ctx

def CSEPass.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  pure (CSE.run ctx op)

end CSE

public def CSEPass : Pass OpCode :=
  { name := "cse"
    description := "Eliminate common memory-independent SSA expressions."
    run := fun _ => CSE.CSEPass.impl }

end Veir
