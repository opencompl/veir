module

public import Veir.Pass
import Std

namespace Veir

/-!
  # Lowering LLVM branches to RISC-V

  The pass has a pure core, `convertModule`, written with folds over lists so
  that it can be reasoned about, and a thin `IO` wrapper around it.

  It works in two phases. First every `llvm.br` and `llvm.cond_br` is replaced
  by a RISC-V branch whose operands are cast to registers, and every
  `llvm.unreachable` by `riscv_cf.unreachable`. Then the arguments
  of every block that is branched to become registers, with a cast back to
  their original type at the start of the block.

  A branch is left alone, together with the blocks it targets, when its
  operands do not fit a register or when a target is also reached by a terminator
  the pass does not rewrite. In strict mode, the default, the pass then
  fails; with `strict=false` the branch survives alongside the lowered ones.
-/

/-- Whether a value of type `type` fits into a register without losing information. -/
@[expose]
public def fitsRegister (type : TypeAttr) : Bool :=
  match type.val with
  | .integerType intType => 0 < intType.bitwidth && intType.bitwidth ≤ 64
  | .byteType byteType => 0 < byteType.bitwidth && byteType.bitwidth ≤ 64
  | .llvmPointerType _ => true
  -- FIXME: Too conservative for structs. The RISC-V calling convention passes a
  -- struct of up to 8 bytes in one register and of up to 16 bytes in two. The
  -- lowering has to split such a struct into its registers in front of the
  -- branch and reassemble it in the successor before it can be admitted here.
  | _ => false

/--
  Cast `operand` to a register with a cast inserted at `ip`, and append the
  cast to `casts`.
-/
def castToReg (ip : InsertPoint) (acc : WfIRContext OpCode × Array OperationPtr)
    (operand : ValuePtr) : Except String (WfIRContext OpCode × Array OperationPtr) := do
  let (ctx, casts) := acc
  let some (ctx, cast) := WfRewriter.createOp! ctx
    Builtin.unrealized_conversion_cast #[RegisterType.mk] #[operand] #[]
    #[] default ip | throw "isel-br-riscv64: cannot cast a branch operand to a register"
  return (ctx, casts.push cast)

/-- Whether `op` is a branch the pass rewrites, or a RISC-V branch that is already lowered. -/
def isLoweredBranch (ctx : WfIRContext OpCode) (op : OperationPtr) : Bool :=
  match op.getOpType! ctx.raw with
  | .llvm .br | .llvm .cond_br | .riscv_cf _ => true
  | _ => false

/--
  The blocks that a terminator the pass does not rewrite branches to. Their
  arguments keep their types, since that terminator keeps passing them.
-/
def blockedTargets (ctx : WfIRContext OpCode) : List BlockPtr :=
  ctx.raw.operations.keys.flatMap fun op =>
    if isLoweredBranch ctx op then [] else (op.getSuccessors! ctx.raw).toList

/-- Whether the arguments of `block` all fit a register, so it can be converted. -/
def isConvertible (ctx : WfIRContext OpCode) (block : BlockPtr) : Bool :=
  (List.range (block.getNumArguments! ctx.raw)).all fun i =>
    fitsRegister ((ValuePtr.blockArgument { block := block, index := i }).getType! ctx.raw)

/--
  Remove from `convertible` the targets of every `llvm.br` and `llvm.cond_br`
  among `ops` that has a target outside of it. Such a branch is left alone and
  keeps passing values of their original types, so none of its targets may be
  converted. Removing a block can leave another branch alone, so this repeats
  until nothing changes, at most `fuel` times.
-/
def dropTargetsOfUnlowered (ctx : WfIRContext OpCode) (ops : List OperationPtr) :
    Nat → List BlockPtr → List BlockPtr
  | 0, convertible => convertible
  | fuel + 1, convertible =>
    let dropped := ops.flatMap fun op =>
      let opType := op.getOpType! ctx
      let targets := (op.getSuccessors! ctx.raw).toList
      if (opType = OpCode.llvm .br || opType = OpCode.llvm .cond_br) &&
          !targets.all convertible.contains then targets else []
    if dropped.any convertible.contains then
      dropTargetsOfUnlowered ctx ops fuel (convertible.filter (!dropped.contains ·))
    else
      convertible

/--
  Replace the terminator `op` by its RISC-V counterpart if it is an `llvm.br`,
  an `llvm.cond_br` or an `llvm.unreachable`, and leave any other operation
  alone. The operands are cast to registers in front of the new branch. A
  branch to a block that cannot be converted is left alone as well.
-/
def convertBranch (convertible : BlockPtr → Bool) (ctx : WfIRContext OpCode) (op : OperationPtr)
    : Except String (WfIRContext OpCode) := do
  let opType := op.getOpType! ctx
  if opType = OpCode.llvm .unreachable then
    let some (ctx, _) := WfRewriter.createOp! ctx Riscv_Cf.unreachable #[] #[]
      #[] #[] () (InsertPoint.before op)
      | throw "isel-br-riscv64: cannot create riscv_cf.unreachable"
    return WfRewriter.eraseOp! ctx op
  if opType != OpCode.llvm .br && opType != OpCode.llvm .cond_br then
    return ctx
  if !(op.getSuccessors! ctx.raw).all convertible then
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

  let ctx := WfRewriter.setType! ctx bap (RegisterType.mk)
  let ip := InsertPoint.atStart! block ctx.raw
  let some (ctx, cast) := WfRewriter.createOp! ctx
    (OpCode.builtin .unrealized_conversion_cast)
    #[origType] #[] #[] #[] default ip
    | throw "isel-br-riscv64: cannot cast a block argument back to its type"
  let ctx := WfRewriter.replaceValue! ctx bap (cast.getResult 0)
  return WfRewriter.pushOperand! ctx cast bap

/--
  Turn the arguments of `block` into registers, unless nothing branches to it
  or it cannot be converted.
-/
def convertBlock (convertible : BlockPtr → Bool) (ctx : WfIRContext OpCode) (block : BlockPtr)
    : Except String (WfIRContext OpCode) := do
  -- If nothing branches to the block (e.g., the entry block) we can skip it.
  if !block.hasPredecessor! ctx.raw then
    return ctx
  if !convertible block then
    return ctx
  -- Add casts in order of block arguments
  (List.range (block.getNumArguments! ctx.raw)).reverse.foldlM (convertBlockArgument block) ctx

/--
  The pure core of the pass. The operations and blocks to visit, and the blocks
  that can be converted, are fixed up front, so the operations the pass creates
  are not visited again.
-/
def convertModule (ctx : WfIRContext OpCode) : Except String (WfIRContext OpCode) := do
  let ops := ctx.raw.operations.keys
  let blocks := ctx.raw.blocks.keys
  let blocked := blockedTargets ctx
  -- Each round that changes something removes a block, so this many suffice.
  let convertible := dropTargetsOfUnlowered ctx ops (blocks.length + 1)
    (blocks.filter fun block => !blocked.contains block && isConvertible ctx block)
  let ctx ← ops.foldlM (convertBranch convertible.contains) ctx
  blocks.foldlM (convertBlock convertible.contains) ctx

/-! # Pass implementation -/

def ISelBrPass.impl (strict : Bool) (ctx : WfIRContext OpCode) (op : OperationPtr)
    (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) := do
  let ctx ← match convertModule ctx with
    | .ok ctx => pure ctx
    | .error message => throw message
  -- In strict mode, no branch but a RISC-V one may remain.
  if strict then
    for o in ctx.raw.operations.keys do
      if !isLoweredBranch ctx o && o.getNumSuccessors! ctx.raw ≠ 0 then
        throw "isel-br-riscv64: cannot lower a branch other than llvm.br or llvm.cond_br"
    for o in ctx.raw.operations.keys do
      let opType := o.getOpType! ctx.raw
      if opType = OpCode.llvm .br || opType = OpCode.llvm .cond_br then
        throw "isel-br-riscv64: a branch operand does not fit a register"
  return ctx

public def IselBrRISCV64 : Pass OpCode :=
  { name := "isel-br-riscv64"
    description :=
      "Lower LLVM IR branch instructions to RISCV 64 assembly."
    options := .ofList [
      ("strict", { description := "Fail if not all branches could be lowered.",
                   defaultValue := true })]
    run := fun options => ISelBrPass.impl ((options.get? "strict").getD true) }
