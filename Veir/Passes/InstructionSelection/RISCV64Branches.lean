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
  `func.call` whose lowering is known to be correct (see `canLowerCall`) by
  `riscv_cf.call`, with its operands cast to registers and its result cast
  back. Other calls are left alone. Then the arguments of every block that is branched to
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
  Argument and result attributes that say something about a value but do not
  change how it is passed. Anything else, such as `byval` or `sret`, might.
-/
def abiNeutralArgAttrs : List String :=
  ["noundef", "nonnull", "dereferenceable", "dereferenceable_or_null", "align",
   "noalias", "nocapture", "captures", "readonly", "writeonly", "readnone",
   "nofree", "returned"].map ("llvm." ++ ·)

/--
  Whether a value of type `type` fills a register exactly, so that passing it
  in one needs no extension and no splitting.
-/
def isRegisterSized (type : Attribute) : Bool :=
  match type with
  | .integerType ⟨64⟩ | .llvmPointerType _ => true
  | _ => false

/--
  Whether the direct call `op`, whose attributes other than its callee are
  `extra`, is one `riscv_cf.call` passes correctly under the standard calling
  convention: at most eight arguments and one result, each an `i64` or a
  pointer, no attribute that changes how they are passed, the C calling
  convention, no operand bundles, and no guaranteed tail call. A variadic call
  is fine, as integer variadic arguments of this size go in a0-a7 just like
  named ones.
-/
def canLowerCall (ctx : WfIRContext OpCode) (op : OperationPtr) (extra : DictionaryAttr) :
    Bool :=
  let attr? (key : String) := (extra.entries.find? (·.1 == key.toUTF8)).map (·.2)
  let neutralAttrs (attrs : Option Attribute) :=
    match attrs with
    | none => true
    | some (.arrayAttr dicts) => dicts.value.all fun
      | .dictionaryAttr dict => dict.entries.all (abiNeutralArgAttrs.contains <| String.fromUTF8! ·.1)
      | _ => false
    | some _ => false
  let operands := (List.range (op.getNumOperands! ctx.raw)).map (op.getOperand! ctx.raw ·)
  operands.length ≤ 8 &&
  op.getNumResults! ctx.raw ≤ 1 &&
  operands.all (fun v => isRegisterSized (v.getType! ctx.raw).val) &&
  (op.getResultTypes! ctx.raw).all (fun t => isRegisterSized t.val) &&
  neutralAttrs (attr? "arg_attrs") &&
  neutralAttrs (attr? "res_attrs") &&
  (match attr? "CConv" with
   | none => true
   | some (.cconvAttr cconv) => cconv.value == "ccc"
   | some _ => false) &&
  (match attr? "op_bundle_sizes" with
   | none => true
   | some (.denseArrayAttr sizes) => sizes.values.isEmpty
   | some _ => false) &&
  (match attr? "TailCallKind" with
   | some (.tailCallKindAttr kind) => kind.value != "musttail"
   | _ => true)

/--
  Replace `op` by its RISC-V counterpart if it is an `llvm.br`, an
  `llvm.cond_br`, an `llvm.unreachable`, or a direct call that `canLowerCall`
  accepts, and leave any other operation alone. The operands of a branch are
  cast to registers in front of the new branch.
-/
def convertBranch (ctx : WfIRContext OpCode) (op : OperationPtr)
    : Except String (WfIRContext OpCode) := do
  let opType := op.getOpType! ctx
  match opType with
  | .llvm .call =>
    let props : LLVMCallProperties := op.getProperties! ctx.raw (OpCode.llvm .call)
    match props.callee with
    | some callee =>
      if canLowerCall ctx op props.extra then return (← convertCall ctx op callee)
      else return ctx
    | none => return ctx
  | .func .call =>
    let props : FuncCallProperties := op.getProperties! ctx.raw (OpCode.func .call)
    if canLowerCall ctx op props.extra then return (← convertCall ctx op props.callee)
    else return ctx
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
