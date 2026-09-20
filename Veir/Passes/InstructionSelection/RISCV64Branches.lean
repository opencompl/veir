module

public import Veir.Pass
import Std

namespace Veir

/-!
  # Lowering LLVM branches to RISC-V

  The pass has a pure core, `convertModule`, written with folds over lists so
  that it can be reasoned about, and a thin `IO` wrapper around it.

  It works in two phases. First every `llvm.br` and `llvm.cond_br` is replaced
  by a RISC-V branch whose operands are cast to registers. Then the arguments
  of every block that is branched to become registers, with a cast back to
  their original type at the start of the block.

  The pass rejects a module it cannot lower correctly: a value passed along a
  branch must fit a register, a terminator with successors must be one of the
  two LLVM branches, and the entry block of a region must not be branched to.
-/

/--
  Whether a value of type `type` survives the round trip through a register:
  a non-empty integer or a byte of at most 64 bits, or a pointer.
-/
@[expose]
public def fitsRegister (type : TypeAttr) : Bool :=
  match type.val with
  | .integerType intType => 0 < intType.bitwidth && intType.bitwidth ≤ 64
  | .byteType byteType => byteType.bitwidth ≤ 64
  | .llvmPointerType _ => true
  | _ => false

/--
  Cast `operand` to a register with a cast inserted at `ip`, and append the
  cast to `casts`.
-/
def castToReg (ip : InsertPoint) (acc : WfIRContext OpCode × Array OperationPtr)
    (operand : ValuePtr) : Except String (WfIRContext OpCode × Array OperationPtr) := do
  let (ctx, casts) := acc
  if !fitsRegister (operand.getType! ctx.raw) then
    throw "isel-br-riscv64: a branch operand does not fit a register"
  let some (ctx, cast) := WfRewriter.createOp! ctx
    Builtin.unrealized_conversion_cast #[RegisterType.mk] #[operand] #[]
    #[] default ip | throw "isel-br-riscv64: cannot cast a branch operand to a register"
  return (ctx, casts.push cast)

/--
  Replace the terminator `op` by its RISC-V counterpart if it is an `llvm.br`
  or an `llvm.cond_br`. The operands are cast to registers in front of the new
  branch. Any other operation is left alone, and must not have successors,
  since the arguments of its successors would become registers.
-/
def convertBranch (ctx : WfIRContext OpCode) (op : OperationPtr)
    : Except String (WfIRContext OpCode) := do
  let opType := op.getOpType! ctx
  if opType != OpCode.llvm .br && opType != OpCode.llvm .cond_br then
    if op.getNumSuccessors! ctx.raw ≠ 0 then
      throw "isel-br-riscv64: only llvm.br and llvm.cond_br may have successors"
    return ctx

  let ip := InsertPoint.before op
  let operands := (List.range (op.getNumOperands! ctx.raw)).map (op.getOperand! ctx.raw ·)
  let successors := op.getSuccessors! ctx.raw
  let (ctx', casts) ← operands.foldlM (castToReg ip) (ctx, #[])
  let regs := casts.map (fun cast => cast.getResult 0)

  let ctx' ←
    if opType = OpCode.llvm .br then do
      let some (ctx', _) := WfRewriter.createOp! ctx' Riscv_Cf.branch #[] regs
        #[op.getSuccessor! ctx.raw 0] #[] default ip
        | throw "isel-br-riscv64: cannot create riscv_cf.branch"
      pure ctx'
    else do
      let condProps : LLVMCondBrProperties := op.getProperties! ctx.raw (OpCode.llvm .cond_br)
      let props : RISCVBrProperties := ⟨condProps.operandSegmentSizes⟩
      let some (ctx', _) := WfRewriter.createOp! ctx' Riscv_Cf.bnez #[] regs
        successors #[] props ip
        | throw "isel-br-riscv64: cannot create riscv_cf.bnez"
      pure ctx'

  if op.getNumRegions! ctx'.raw = 0 && !op.hasUses! ctx'.raw then
    return WfRewriter.eraseOp! ctx' op
  return ctx'

/--
  Turn argument `i` of `block` into a register. A cast at the start of the
  block gives the rest of the block the value at its original type.
-/
def convertBlockArgument (block : BlockPtr) (ctx : WfIRContext OpCode) (i : Nat)
    : Except String (WfIRContext OpCode) := do
  let bap : BlockArgumentPtr := { block := block, index := i }

  -- preserving the block argument's original type so the cast back from the
  -- register reproduces the correct type (e.g. i32 instead of i64)
  let origType := (ValuePtr.blockArgument bap).getType! ctx.raw
  if !fitsRegister origType then
    throw "isel-br-riscv64: a block argument does not fit a register"

  let ctx := WfRewriter.setType! ctx bap (RegisterType.mk)
  let ip := InsertPoint.atStart! block ctx.raw
  let some (ctx, cast) := WfRewriter.createOp! ctx
    (OpCode.builtin .unrealized_conversion_cast)
    #[origType] #[] #[] #[] default ip
    | throw "isel-br-riscv64: cannot cast a block argument back to its type"
  let ctx := WfRewriter.replaceValue! ctx bap (cast.getResult 0)
  return WfRewriter.pushOperand! ctx cast bap

/-- Turn the arguments of `block` into registers, unless nothing branches to it. -/
def convertBlock (ctx : WfIRContext OpCode) (block : BlockPtr)
    : Except String (WfIRContext OpCode) := do
  -- If the block has no uses (e.g., the entry block) we can skip it.
  if (block.get! ctx.raw).firstUse == none then
    return ctx
  -- The arguments of an entry block are those of the enclosing operation.
  if let some region := (block.get! ctx.raw).parent then
    if (region.get! ctx.raw).firstBlock == some block then
      throw "isel-br-riscv64: the entry block of a region is branched to"
  (List.range (block.getNumArguments! ctx.raw)).foldlM (convertBlockArgument block) ctx

/--
  The pure core of the pass. The operations and blocks to visit are fixed up
  front, so the operations the pass creates are not visited again.
-/
def convertModule (ctx : WfIRContext OpCode) : Except String (WfIRContext OpCode) := do
  let ops := ctx.raw.operations.keys
  let blocks := ctx.raw.blocks.keys
  let ctx ← ops.foldlM convertBranch ctx
  blocks.foldlM convertBlock ctx

/-! # Pass implementation -/

def ISelBrPass.impl (ctx : WfIRContext OpCode) (op : OperationPtr)
    (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) :=
  match convertModule ctx with
  | .ok ctx => return ctx
  | .error message => throw message

public def IselBrRISCV64 : Pass OpCode :=
  { name := "isel-br-riscv64"
    description :=
      "Lower LLVM IR branch instructions to RISCV 64 assembly."
    run := fun _ => ISelBrPass.impl }
