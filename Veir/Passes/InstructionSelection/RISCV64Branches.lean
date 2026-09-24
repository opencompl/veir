module

public import Veir.Pass
import Std

namespace Veir

/-!
  # Lowering LLVM control flow to RISC-V

  The pass has a pure core, `convertModule`, written with folds over lists so
  that it can be reasoned about, and a thin `IO` wrapper around it.

  It works in two phases. First every `llvm.br` and `llvm.cond_br` is replaced
  by a RISC-V branch whose operands are cast to registers, every
  `llvm.unreachable` by `riscv_cf.unreachable`, and every direct `llvm.call` or
  `func.call` by `riscv_cf.call`, with its operands cast to registers and its
  result cast back. Then the arguments of every block that is branched to
  become registers, with a cast back to their original type at the start of the
  block.

  Returns are left alone: `coerce-function-boundaries-to-riscv-reg` lowers them
  to `riscv_cf.ret` once it has coerced the function's signature.
-/

/--
  Cast `operand` to a register with a cast inserted at `ip`, and append the
  cast to `casts`.
-/
def castToReg (ip : InsertPoint) (acc : WfIRContext OpCode × Array OperationPtr)
    (operand : ValuePtr) : Except String (WfIRContext OpCode × Array OperationPtr) := do
  let (ctx, casts) := acc
  let some (ctx, cast) := WfRewriter.createOp! ctx
    Builtin.unrealized_conversion_cast #[RegisterType.mk] #[operand] #[]
    #[] default ip | throw "isel-br-riscv64: cannot cast an operand to a register"
  return (ctx, casts.push cast)

/--
  Replace a direct call `op` by a `riscv_cf.call`. The arguments are cast to
  registers in front of the call, and its result, if any, is cast back to its
  original type after it.
-/
def convertCall (ctx : WfIRContext OpCode) (op : OperationPtr) (callee : FlatSymbolRefAttr)
    : Except String (WfIRContext OpCode) := do
  let ip := InsertPoint.before op
  let operands := (List.range (op.getNumOperands! ctx.raw)).map (op.getOperand! ctx.raw ·)
  let (ctx, casts) ← operands.foldlM (castToReg ip) (ctx, #[])
  let regs := casts.map (fun cast => cast.getResult 0)
  let resultTypes := op.getResultTypes! ctx.raw
  let some (ctx, call) := WfRewriter.createOp! ctx Riscv_Cf.call
    (resultTypes.map fun _ => RegisterType.mk) regs #[] #[] ({ callee } : RISCVCallProperties) ip
    | throw "isel-br-riscv64: cannot create riscv_cf.call"
  let ctx ← (List.range resultTypes.size).foldlM (fun ctx i => do
    let some (ctx, cast) := WfRewriter.createOp! ctx
      Builtin.unrealized_conversion_cast #[resultTypes[i]!] #[call.getResult i] #[]
      #[] default ip
      | throw "isel-br-riscv64: cannot cast a call result back to its type"
    return WfRewriter.replaceValue! ctx (op.getResult i) (cast.getResult 0)) ctx
  return WfRewriter.eraseOp! ctx op

/--
  Replace `op` by its RISC-V counterpart if it is an `llvm.br`, an
  `llvm.cond_br`, an `llvm.unreachable`, or a direct call, and leave any other
  operation alone. The operands of a branch are cast to registers in front of
  the new branch.
-/
def convertBranch (ctx : WfIRContext OpCode) (op : OperationPtr)
    : Except String (WfIRContext OpCode) := do
  let opType := op.getOpType! ctx
  match opType with
  | .llvm .call =>
    let props : LLVMCallProperties := op.getProperties! ctx.raw (OpCode.llvm .call)
    match props.callee with
    | some callee => return (← convertCall ctx op callee)
    | none => return ctx
  | .func .call =>
    let props : FuncCallProperties := op.getProperties! ctx.raw (OpCode.func .call)
    return (← convertCall ctx op props.callee)
  | .llvm .unreachable =>
    let some (ctx, _) := WfRewriter.createOp! ctx Riscv_Cf.unreachable #[] #[] #[] #[] ()
      (InsertPoint.before op)
      | throw "isel-br-riscv64: cannot create riscv_cf.unreachable"
    return WfRewriter.eraseOp! ctx op
  | .llvm .br | .llvm .cond_br => pure ()
  | _ => return ctx

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
      "Lower LLVM IR branches, calls, and unreachable to RISCV 64 assembly."
    run := fun _ => ISelBrPass.impl }
