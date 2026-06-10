import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching
import Veir.Rewriter.WfRewriter
import Veir.Rewriter.WfRewriter
import Veir.Printer
import Veir.Properties
import Std


namespace Veir

set_option warn.sorry false in
def convertBlock (ctx : WfIRContext OpCode) (block : BlockPtr) : ExceptT String IO (WfIRContext OpCode) := do
  let argCount := block.getNumArguments! ctx.raw
  let mut c := ctx.raw

  -- If the block has no uses (e.g., the entry block) we can skip it.
  if (block.get! c).firstUse == none then
    return ⟨c, by sorry⟩

  let mut currentPredUse := (block.get! c).firstUse
  while let some block := currentPredUse do
    have op := (block.get! ctx.raw).owner
    currentPredUse := (block.get! ctx.raw).nextUse

    -- Check if the terminator operations can be converted to RISCV branches. If
    -- not, we exit early and do not convert this predecessor block.
    if op.getOpType! ctx.raw != .llvm .br && op.getOpType! ctx.raw != .llvm .cond_br then
      continue

    -- TODO: it seems we have some dangling operations which we need to ignore to
    -- make things work. Eventually, these should be removed such that they are not
    -- even dangling.
    let some block := (op.get! c).parent | continue

    let mut ip := InsertPoint.after op ctx.raw block sorry sorry
    let mut casts : Array (OperationPtr) := #[]

    for i in List.reverse (List.range (op.getNumOperands! ctx.raw)) do
      let operand := op.getOperand! ctx.raw i
      let some (xc, cast) := Rewriter.createOp c (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[operand] #[] #[] default ip sorry sorry sorry sorry sorry | return ⟨c, by sorry⟩
      c := xc
      casts := casts.push cast

    let some (xc, newop ) :=
    if h : op.getOpType! ctx.raw = .llvm .br then do
      Rewriter.createOp c (.riscv_cf .branch) #[] (casts.map (fun cast => cast.getResult 0)) #[op.getSuccessor c 0 sorry sorry] #[] default ip sorry sorry sorry sorry sorry
    else if h : op.getOpType! ctx.raw = .llvm .cond_br then do
      let condProps : CondBrProperties := op.getProperties! c (.llvm .cond_br)
      let props : RISCVBrProperties := ⟨condProps.operandSegmentSizes⟩
      Rewriter.createOp c (.riscv_cf .cbr) #[] (casts.map (fun cast => cast.getResult 0)) (op.getSuccessors c sorry) #[] props ip sorry sorry sorry sorry sorry
    else
      none | return ⟨c, by sorry⟩

    c := Rewriter.detachOp xc op sorry sorry sorry

  for i in List.range (block.getNumArguments! c) do
    let bap : BlockArgumentPtr := { block := block, index := i }

    c := Rewriter.setType c bap (RegisterType.mk) sorry
    let ip := InsertPoint.atStart block c sorry
    let some (xc, cast) := Rewriter.createEmptyOp c (.builtin .unrealized_conversion_cast) default | return ⟨c, by sorry⟩
    let some xc := Rewriter.insertOp? xc cast ip sorry sorry sorry | return ⟨c, by sorry⟩
    c := Rewriter.pushResult xc cast (IntegerType.mk 64) sorry
    let some (xc) := Rewriter.replaceValue? c bap (cast.getResult 0) sorry sorry sorry | return ⟨c, by sorry⟩
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
