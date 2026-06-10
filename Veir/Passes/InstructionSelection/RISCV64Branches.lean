import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching
import Veir.Rewriter.WfRewriter
import Veir.Rewriter.WfRewriter
import Veir.Printer
import Std


namespace Veir

open Std.Iterators

structure PredBlockIterator where
  ctx : WfIRContext OpCode
  currentUse : Option BlockOperandPtr

instance : Std.Iterator PredBlockIterator Id BlockOperandPtr where
  IsPlausibleStep it
    | .yield it' out => --it.internalState.ctx = it'.internalState.ctx ∧
                       -- it.internalState.currentUse = some out ∧
                        it'.internalState.currentUse = (if let some x := it.internalState.currentUse then (x.get! it.internalState.ctx.raw).nextUse else none)
    | .skip _ => False
    | .done => it.internalState.currentUse = none
  step it := pure (match it.internalState.currentUse with
        | none => .deflate ⟨.done, rfl⟩
        | some use => .deflate ⟨.yield ⟨it.internalState.ctx, (use.get! it.internalState.ctx.raw).nextUse⟩ use,
        rfl⟩)

private def PredBlockIterator.instFinitenessRelation [Pure m] :
    Std.Iterators.FinitenessRelation PredBlockIterator Id where
  Rel := sorry
  wf := sorry --InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    sorry

instance PredBlockIterator.instFinite: Std.Iterators.Finite PredBlockIterator Id := sorry

def PredBlockIterator.iterM (l : BlockPtr)  (ctx : WfIRContext OpCode)  (m : Type → Type) :
    Std.IterM (α := PredBlockIterator) m BlockOperandPtr :=
  ⟨ctx, (l.get! ctx.raw).firstUse⟩

def PredBlockIterator.iter (l : BlockPtr) (ctx : WfIRContext OpCode) :
     Std.Iter (α := PredBlockIterator) BlockOperandPtr :=
  PredBlockIterator.iterM l ctx Id |>.toIter

def convertBlock (ctx : WfIRContext OpCode) (block : BlockPtr) : ExceptT String IO (WfIRContext OpCode) := do
  let argCount := block.getNumArguments! ctx.raw
  let mut c := ctx.raw
  if (block.get! ctx.raw).firstUse == none then
    -- If the block has no uses (e.g., the entry block) we can skip it.
    return ⟨c, by sorry⟩

  if (PredBlockIterator.iter block ctx).toList.length = 0 then
    return ⟨c, by sorry⟩

  for block in (PredBlockIterator.iter block ctx).toList do
    have op := (block.get! ctx.raw).owner

    -- Check if the terminator operations can be converted to RISCV branches. If not,
    -- we skip converting this predecessor block.
    if op.getOpType! ctx.raw != .llvm .br && op.getOpType! ctx.raw != .llvm .cond_br then
      continue

    -- TODO: it seems we have some dangling operations which we need to ignore to
    -- make things work. Eventually, these should be removed such that they are not
    -- even dangling.
    if (op.get! ctx.raw).parent = none then
      continue

    let some block := (op.get! ctx.raw).parent | return ⟨c, by sorry⟩
    let mut ip := InsertPoint.after op ctx.raw block sorry sorry
    let mut casts : Array (OperationPtr) := #[]

    for i in List.reverse (List.range (op.getNumOperands! ctx.raw)) do
      let operand := op.getOperand! ctx.raw i
      let some (xc, cast) := Rewriter.createOp c (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[operand] #[] #[] default ip sorry sorry sorry sorry sorry | return ⟨c, by sorry⟩
      c := xc
      casts := casts.push cast

    let some (xc, newop ) :=
    if op.getOpType! ctx.raw = .llvm .br then do
      Rewriter.createOp c (.riscv_cf .branch) #[] (casts.map (fun cast => cast.getResult 0)) #[op.getSuccessor c 0 sorry sorry] #[] default ip sorry sorry sorry sorry sorry
    else
      Rewriter.createOp c (.riscv_cf .bne) #[] (casts.map (fun cast => cast.getResult 0)) (op.getSuccessors c sorry) #[] default ip sorry sorry sorry sorry sorry | return ⟨c, by sorry⟩
    c := Rewriter.detachOp xc op sorry sorry sorry

  for i in List.range (block.getNumArguments! c) do
    let bap : BlockArgumentPtr := { block := block, index := i }

    c := Rewriter.setType c bap (RegisterType.mk) sorry
    let ip := InsertPoint.atStart block c sorry
    let some (xc, cast) := Rewriter.createEmptyOp c (.builtin .unrealized_conversion_cast) default | return ⟨c, by sorry⟩
    let vp : ValuePtr := cast.getResult 0
    let some xc := Rewriter.insertOp? xc cast ip sorry sorry sorry | return ⟨c, by sorry⟩
    c := Rewriter.pushResult xc cast (IntegerType.mk 64) sorry

    let some (xc) := Rewriter.replaceValue? c bap vp sorry sorry sorry | return ⟨c, by sorry⟩
    c := xc

    c := Rewriter.pushOperand c cast bap sorry sorry sorry
  return ⟨c, by sorry⟩

def convertModule (ctx : WfIRContext OpCode) :
    ExceptT String IO (WfIRContext OpCode) := do
  let mut c := ctx
  for block in ctx.raw.blocks.keys do
     c := ← convertBlock c block
  return c

/-! # Pass implementation -/

def ISelBrPass.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  return (← convertModule ctx)

public def IselBrRISCV64 : Pass OpCode :=
  { name := "isel-br-riscv64"
    description :=
      "Lower LLVM IR branch instructions to RISCV 64 assembly."
    run := ISelBrPass.impl }
