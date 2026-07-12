import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching
import Veir.Rewriter.WfRewriter
import Veir.Printer
import Veir.Properties
import Std

namespace Veir

def convertBranch (ctx : WfIRContext OpCode) (op : OperationPtr)
    : ExceptT String IO (WfIRContext OpCode) := do
  let mut c := ctx

  -- Check if the terminator operations can be converted to RISCV branches. If
  -- not, we exit early and do not convert this predecessor block.
  if op.getOpType! c != OpCode.llvm .br &&
     op.getOpType! c != OpCode.llvm .cond_br then do
    return c

  let mut ip := InsertPoint.before op
  let mut casts : Array (OperationPtr) := #[]

  for i in List.range (op.getNumOperands! c.raw) do
    let operand := op.getOperand! c.raw i
    let some (c', cast) := WfRewriter.createOp! c
      (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[operand] #[]
      #[] default ip | return c
    c := c'
    casts := casts.push cast

  if op.getOpType! c = OpCode.llvm .br then do
    let some (c', _) := WfRewriter.createOp! c (.riscv_cf .branch) #[]
      (casts.map (fun cast => cast.getResult 0))
      #[op.getSuccessor! c.raw 0] #[] default ip | return c
    c := c'

  if op.getOpType! c = OpCode.llvm .cond_br then do
    let condProps : CondBrProperties := op.getProperties! c
      (OpCode.llvm .cond_br)
    let props : RISCVBrProperties := ⟨condProps.operandSegmentSizes⟩

    let some (c', _) := WfRewriter.createOp! c (.riscv_cf .bnez) #[]
      (casts.map (fun cast => cast.getResult 0))
      (op.getSuccessors! c.raw) #[] props ip | return c
    c := c'

  if op.getNumRegions! c.raw = 0 && !op.hasUses! c.raw then
    c := WfRewriter.eraseOp! c op

  return c

def convertBlock (ctx : WfIRContext OpCode) (block : BlockPtr)
    : ExceptT String IO (WfIRContext OpCode) := do
  let mut c := ctx

  -- If the block has no uses (e.g., the entry block) we can skip it.
  if (block.get! c.raw).firstUse == none then
    return c

  -- convertBranch mutates the IR, so we build predOps first, to avoid
  -- data structure invalidation issues
  let mut predOps : Array OperationPtr := #[]
  let mut currentPredUse := (block.get! c.raw).firstUse
  while let some blockop := currentPredUse do
    let blockOperand := blockop.get! c.raw
    let op := blockOperand.owner
    currentPredUse := blockOperand.nextUse
    if !predOps.contains op then
      predOps := predOps.push op

  for op in predOps do
    c := ← convertBranch c op

  for i in List.range (block.getNumArguments! c.raw) do
    let bap : BlockArgumentPtr := { block := block, index := i }

    -- preserving the block argument's original type so the cast back from the
    -- register reproduces the correct type (e.g. i32 instead of i64)
    let origType := (ValuePtr.blockArgument bap).getType! c.raw

    c := WfRewriter.setType! c bap (RegisterType.mk)
    let ip := InsertPoint.atStart! block c.raw
    let some (c', cast) := WfRewriter.createOp! c
      (OpCode.builtin .unrealized_conversion_cast)
      #[origType] #[] #[] #[] default ip | return c
    let c' := WfRewriter.replaceValue! c' bap (cast.getResult 0)
    c := WfRewriter.pushOperand! c' cast bap

  return c

def convertModule (ctx : WfIRContext OpCode) :
    ExceptT String IO (WfIRContext OpCode) := do
  let mut c := ctx
  for block in ctx.raw.blocks.keys do
     c := ← convertBlock c block
  return c

/-! # Pass implementation -/

def ISelBrPass.impl (ctx : WfIRContext OpCode) (op : OperationPtr)
    (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) := do
  return (← convertModule ctx)

public def IselBrRISCV64 : Pass OpCode :=
  { name := "isel-br-riscv64"
    description :=
      "Lower LLVM IR branch instructions to RISCV 64 assembly."
    run := ISelBrPass.impl }
