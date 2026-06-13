import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching
import Veir.Rewriter.WfRewriter
import Veir.Printer
import Veir.Properties
import Std


namespace Veir

def convertBranch (ctx : WfIRContext OpCode) (op : OperationPtr)
    (block : BlockPtr) : ExceptT String IO (WfIRContext OpCode) := do
  let mut c := ctx

   -- Check if the terminator operations can be converted to RISCV branches. If
   -- not, we exit early and do not convert this predecessor block.
   if op.getOpType! c.raw != .llvm .br && op.getOpType! c.raw != .llvm .cond_br then
     return c

   let mut some ip := InsertPoint.after? op c.raw | return c
   let mut casts : Array (OperationPtr) := #[]

   for i in List.reverse (List.range (op.getNumOperands! c.raw)) do
     let operand := op.getOperand! c.raw i
     let some (c', cast) := WfRewriter.createOp c
       (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[operand] #[]
       #[] default ip sorry sorry sorry sorry | return c
     c := c'
     casts := casts.push cast

   let some (c', _) :=
   if h : op.getOpType! c = OpCode.llvm .br then do
     WfRewriter.createOp c (.riscv_cf .branch) #[]
       (casts.map (fun cast => cast.getResult 0))
       #[op.getSuccessor c.raw 0 sorry sorry] #[] default ip sorry sorry sorry
       sorry
   else if h : op.getOpType! c = OpCode.llvm .cond_br then do
     let condProps : CondBrProperties := op.getProperties! c
       (OpCode.llvm .cond_br)
     let props : RISCVBrProperties := ⟨condProps.operandSegmentSizes⟩
     WfRewriter.createOp c (.riscv_cf .bnez) #[]
       (casts.map (fun cast => cast.getResult 0))
       (op.getSuccessors c.raw sorry) #[] props ip sorry sorry sorry sorry
   else
     none | return c

   c := c'

   if h : op.getNumRegions! c.raw = 0 && !op.hasUses! c.raw then
     c := WfRewriter.eraseOp c op (by grind) (by grind) (sorry)

   return c

set_option warn.sorry false in
def convertBlock (ctx : WfIRContext OpCode) (block : BlockPtr)
    : ExceptT String IO (WfIRContext OpCode) := do
  let mut c := ctx

  -- If the block has no uses (e.g., the entry block) we can skip it.
  if (block.get! c.raw).firstUse == none then
    return c

  let mut currentPredUse := (block.get! c.raw).firstUse
  while let some blockop := currentPredUse do
    have op := (blockop.get! c.raw).owner
    currentPredUse := (blockop.get! c.raw).nextUse
    c := ← convertBranch c op block

  for i in List.range (block.getNumArguments! c.raw) do
    let bap : BlockArgumentPtr := { block := block, index := i }

    c := WfRewriter.setType c bap (RegisterType.mk) sorry
    let ip := InsertPoint.atStart block c.raw sorry
    let some (c', cast) := WfRewriter.createOp c
      (OpCode.builtin .unrealized_conversion_cast)
      #[IntegerType.mk 64] #[] #[] #[] default ip sorry sorry sorry
      sorry | return c
    let c' := WfRewriter.replaceValue c' bap (cast.getResult 0) sorry sorry
      sorry
    c := WfRewriter.pushOperand c' cast bap sorry sorry

  return c

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
