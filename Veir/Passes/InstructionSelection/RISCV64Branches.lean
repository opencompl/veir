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
  `llvm.unreachable` by `riscv_cf.unreachable`. Then the arguments of every
  block that such a branch passes values to become registers, with a cast back
  to their original type at the start of the block.

  The pass rejects a module it cannot lower correctly: a value passed along a
  branch must fit a register, and a terminator with successors must be one of
  the two LLVM branches. It expects a module that verifies, in which the entry
  block of a region is not branched to, since the arguments of an entry block
  are those of the enclosing operation and cannot become registers.
-/

/--
  Whether a value of type `type` survives the round trip through a register:
  a non-empty integer or a byte of at most 64 bits, or a pointer.

  A register holds only the address of a pointer, which comes back as the wild
  pointer at that address. That is a refinement when pointers are compared by
  address, as Alive2 does for assembly.
-/
@[expose]
public def fitsRegister (type : TypeAttr) : Bool :=
  match type.val with
  | .integerType intType => 0 < intType.bitwidth && intType.bitwidth ≤ 64
  | .byteType byteType => byteType.bitwidth ≤ 64
  | .llvmPointerType _ => true
  | _ => false

/-- `op` is one of the two LLVM branches that the pass replaces. -/
@[expose]
public def OperationPtr.IsLlvmBranch (op : OperationPtr) (ctx : IRContext OpCode) : Prop :=
  op.getOpType! ctx = .llvm .br ∨ op.getOpType! ctx = .llvm .cond_br

public instance {op : OperationPtr} {ctx : IRContext OpCode} :
    Decidable (op.IsLlvmBranch ctx) := by
  unfold OperationPtr.IsLlvmBranch; infer_instance

/--
  Cast `operand` to a register with a cast inserted at `ip`, and append the
  cast to `casts`.
-/
public def castToReg (ip : InsertPoint) (acc : WfIRContext OpCode × Array OperationPtr)
    (operand : ValuePtr) : Except String (WfIRContext OpCode × Array OperationPtr) :=
  if !fitsRegister (operand.getType! acc.1.raw) then
    throw "isel-br-riscv64: a branch operand does not fit a register"
  else
    match WfRewriter.createOp! acc.1 Builtin.unrealized_conversion_cast #[RegisterType.mk]
      #[operand] #[] #[] default ip with
    | some (ctx, cast) => pure (ctx, acc.2.push cast)
    | none => throw "isel-br-riscv64: cannot cast a branch operand to a register"

/--
  Create in `ctx` the RISC-V branch that replaces `op`, in front of it. It takes
  the registers `regs` and the successors that `op` has in `source`.
-/
public def createRiscvBranch (source : IRContext OpCode) (op : OperationPtr)
    (ctx : WfIRContext OpCode) (regs : Array ValuePtr)
    : Except String (WfIRContext OpCode × OperationPtr) :=
  let ip := InsertPoint.before op
  let successors := op.getSuccessors! source
  if op.getOpType! source = OpCode.llvm .br then
    match WfRewriter.createOp! ctx Riscv_Cf.branch #[] regs successors #[] default ip with
    | some result => pure result
    | none => throw "isel-br-riscv64: cannot create riscv_cf.branch"
  else
    let condProps : LLVMCondBrProperties := op.getProperties! source (OpCode.llvm .cond_br)
    let props : RISCVBrProperties := ⟨condProps.operandSegmentSizes⟩
    match WfRewriter.createOp! ctx Riscv_Cf.bnez #[] regs successors #[] props ip with
    | some result => pure result
    | none => throw "isel-br-riscv64: cannot create riscv_cf.bnez"

/-- Erase the branch `op` that has been replaced. -/
public def eraseBranch (ctx : WfIRContext OpCode) (op : OperationPtr)
    : Except String (WfIRContext OpCode) :=
  if op.getNumRegions! ctx.raw ≠ 0 || op.hasUses! ctx.raw then
    throw "isel-br-riscv64: cannot erase a branch"
  else
    pure (WfRewriter.eraseOp! ctx op)

/--
  Replace the `llvm.br` or `llvm.cond_br` `op` by its RISC-V counterpart. The
  operands are cast to registers in front of the new branch.
-/
public def lowerBranch (ctx : WfIRContext OpCode) (op : OperationPtr)
    : Except String (WfIRContext OpCode) := do
  let operands := (List.range (op.getNumOperands! ctx.raw)).map (op.getOperand! ctx.raw ·)
  let (ctx', casts) ← operands.foldlM (castToReg (InsertPoint.before op)) (ctx, #[])
  let regs := casts.map (fun cast => (cast.getResult 0 : ValuePtr))
  let (ctx', _) ← createRiscvBranch ctx.raw op ctx' regs
  eraseBranch ctx' op

/--
  Replace the terminator `op` by its RISC-V counterpart if it is an `llvm.br`,
  an `llvm.cond_br` or an `llvm.unreachable`. Any other operation is left alone,
  and must not have successors, since the arguments of its successors would
  become registers.
-/
public def convertBranch (ctx : WfIRContext OpCode) (op : OperationPtr)
    : Except String (WfIRContext OpCode) :=
  if op.getOpType! ctx = OpCode.llvm .unreachable then
    match WfRewriter.createOp! ctx Riscv_Cf.unreachable #[] #[] #[] #[] ()
        (InsertPoint.before op) with
    | none => throw "isel-br-riscv64: cannot create riscv_cf.unreachable"
    | some (ctx, _) => pure (WfRewriter.eraseOp! ctx op)
  else if ¬ op.IsLlvmBranch ctx.raw then
    if op.getNumSuccessors! ctx.raw ≠ 0 then
      throw "isel-br-riscv64: only llvm.br and llvm.cond_br may have successors"
    else
      pure ctx
  else if op.getNumResults! ctx.raw ≠ 0 then
    throw "isel-br-riscv64: a branch has results"
  else
    lowerBranch ctx op

/--
  Turn argument `i` of `block` into a register. A cast at the start of the
  block gives the rest of the block the value at its original type.
-/
public def convertBlockArgument (block : BlockPtr) (ctx : WfIRContext OpCode) (i : Nat)
    : Except String (WfIRContext OpCode) :=
  let arg : BlockArgumentPtr := { block := block, index := i }
  -- The cast back from the register reproduces the original type (e.g. i32 instead of i64).
  let origType := (ValuePtr.blockArgument arg).getType! ctx.raw
  if !fitsRegister origType then
    throw "isel-br-riscv64: a block argument does not fit a register"
  else
    let ctx := WfRewriter.setType! ctx arg (RegisterType.mk)
    match WfRewriter.createOp! ctx (OpCode.builtin .unrealized_conversion_cast)
      #[origType] #[] #[] #[] default (InsertPoint.atStart! block ctx.raw) with
    | some (ctx, cast) =>
      let ctx := WfRewriter.replaceValue! ctx arg (cast.getResult 0)
      pure (WfRewriter.pushOperand! ctx cast arg)
    | none => throw "isel-br-riscv64: cannot cast a block argument back to its type"

/-- Turn the arguments of `block` into registers. -/
public def convertBlock (ctx : WfIRContext OpCode) (block : BlockPtr)
    : Except String (WfIRContext OpCode) :=
  (List.range (block.getNumArguments! ctx.raw)).foldlM (convertBlockArgument block) ctx

/-- Convert `block` unless it is among the blocks that are `done`. -/
public def convertBlockOnce (acc : WfIRContext OpCode × List BlockPtr) (block : BlockPtr)
    : Except String (WfIRContext OpCode × List BlockPtr) := do
  if block ∈ acc.2 then
    pure acc
  else do
    let ctx ← convertBlock acc.1 block
    pure (ctx, block :: acc.2)

/-- The blocks that the branches among `ops` pass values to. -/
@[expose]
public def branchTargets (ctx : IRContext OpCode) (ops : List OperationPtr) : List BlockPtr :=
  ops.flatMap fun op => if op.IsLlvmBranch ctx then (op.getSuccessors! ctx).toList else []

/--
  The pure core of the pass. The operations to visit and the blocks they branch
  to are fixed up front, so the operations the pass creates are not visited.
-/
public def convertModule (ctx : WfIRContext OpCode) : Except String (WfIRContext OpCode) := do
  let ops := ctx.raw.operations.keys
  let lowered ← ops.foldlM convertBranch ctx
  let (converted, _) ← (branchTargets ctx.raw ops).foldlM convertBlockOnce (lowered, [])
  return converted

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
