module

public import Veir.Pass
import Veir.Passes.RegisterAllocation.Helper
import Veir.Rewriter.WfRewriter
import Veir.PatternRewriter.Basic

namespace Veir

/-!

This pass precolours function arguments and return values according to the RISC-V calling convention.
It inserts move instructions to isolate them from the rest of the block, so that the later allocation
pass can assign registers to the other values independently.

The function signature and entry-block arguments are updated to use precoloured types, as required
by the `FunctionOpInterface` verifier.

Example:
```
func.func @example(%a: !riscv.reg) -> !riscv.reg {
^entry(%a: !riscv.reg):
  %s = riscv.add %a, %a
  riscv_cf.return %s
}

=>

func.func @example(%a: !riscv.reg<x10>) -> !riscv.reg {
^entry(%a: !riscv.reg<x10>):
  %c = riscv.mv %a : !riscv.reg
  %s = riscv.add %c, %c
  %r = riscv.mv %s : !riscv.reg<x10>
  riscv_cf.return %r
}
```
-/

/--
The allocation state of a value at the function boundary, relative to its pinned register.

Arguments and results are precoloured differently. An argument arrives in its pinned register, so
it cannot be preallocated to any other register. A result can be preallocated to another register and
copied into its pinned return value.
-/
inductive AllocationState where
  /-- Not allocated yet. -/
  | unallocated
  /-- Already in its target register. -/
  | inTarget
  /-- Preallocated to another register. -/
  | preallocated (r : RegisterType)

/--
Return the allocation state of `v` against its pinned register `reg`. `v` must be an integer
register value. `what` refers to the position of `v` (an argument or a result).
-/
private def allocationState (ctx : WfIRContext OpCode) (v : ValuePtr) (reg : RegisterType)
    (what : String) : Except String AllocationState := do
  let .registerType r := (v.getType! ctx.raw).val
    | throw s!"precolouring expects {what} to have an integer register type"
  if r.cls != .int then
    throw s!"precolouring expects {what} to have an integer register type, got {r}"
  if r == reg then return .inTarget
  match r.index with
  | none => return .unallocated
  | some _ => return .preallocated r

/--
Pin each argument `i` of the function `func` to its register `a<i>` (`aRegister i`).

The calling convention is part of the signature, so the assignment is updated there first and
then passed down to the entry block's arguments. Each used argument is copied by a `mv` at the
start of the entry block into a fresh unassigned value, which takes over all of its uses.
-/
def precolourArguments (ctx : WfIRContext OpCode) (func : OperationPtr) :
    Except String (WfIRContext OpCode) := do
  let some funcOp := FunctionOp.of? func ctx.raw | return ctx
  let some entry := funcOp.getEntryBlock? | return ctx
  let n := funcOp.getNumArguments
  let ctx := FunctionOp.setFunctionType! ctx funcOp
    ((Array.range n).map (.registerType <| aRegister ·)) funcOp.getResultTypes
  let mut ctx := ctx
  -- Copies are inserted at the start of the block, so walk the arguments backwards to
  -- leave the copies in argument order.
  for i in (List.range n).reverse do
    let arg : BlockArgumentPtr := { block := entry, index := i }
    let arg' : ValuePtr := .blockArgument arg
    let reg := aRegister i
    ctx := WfRewriter.setType! ctx arg' reg
    if (arg'.getFirstUse! ctx.raw).isNone then continue
    let some (ctx', copy) := WfRewriter.createOp! ctx Riscv.mv #[RegisterType.mk] #[] #[] #[] ()
        (some (InsertPoint.atStart! entry ctx.raw))
      | throw s!"precolouring could not copy argument {i}"
    let ctx' := WfRewriter.replaceValue! ctx' arg' (copy.getResult 0)
    ctx := WfRewriter.pushOperand! ctx' copy arg'
  return ctx

/--
Copy each result returned by the `riscv_cf.return` `ret` into its return value:
- A return value is the operand of `riscv_cf.return`, and must be in `a<i>` (`aRegister i`).
- A result is the value the function computes. It may have a preallocated physical register,
  and is copied into its return value.

The copies run sequentially, so a copy must not overwrite a result that a later copy still
reads:
- An unassigned result is safe: the physical renaming pass (later) excludes `a0`/`a1`.
- A preallocated result can be overwritten. With at most two results, the only case is
  when result 0 is not preallocated to `a0` but result 1 preallocated to `a0`,
  e.g. `return %b, %a` with `%a` in `a0` and `%b` in `a1`. This parallel copy is rejected by
  `checkPrecolourable`.
-/
def precolourReturn (ctx : WfIRContext OpCode) (ret : OperationPtr) :
    Except String (WfIRContext OpCode) := do
  let operands := ret.getOperands! ctx.raw
  let mut ctx := ctx
  for h : i in [0:operands.size] do
    let value := operands[i]
    let reg := aRegister i
    let some (ctx', copy) := WfRewriter.createOp! ctx Riscv.mv #[reg] #[value] #[] #[] ()
        (some (.before ret))
      | throw s!"precolouring could not copy result {i} into its return value"
    ctx := WfRewriter.replaceOperand! ctx' ⟨ret, i⟩ (copy.getResult 0)
  return ctx

/--
Check in `ctx` that precolouring can express the function `func`. A pattern fails without a message,
so the pass runs this on every function before the patterns.
-/
def checkPrecolourable (ctx : WfIRContext OpCode) (func : OperationPtr) : Except String Unit := do
  let some funcOp := FunctionOp.of? func ctx.raw | return
  let some entry := funcOp.getEntryBlock? | return
  checkCallingConvention funcOp
  for i in [0:funcOp.getNumArguments] do
    let reg := aRegister i
    let arg : ValuePtr := .blockArgument { block := entry, index := i }
    if let .preallocated r ← allocationState ctx arg reg s!"argument {i}" then
      throw s!"illegal register allocation of function arguments: argument {i} cannot be passed \
        in {r}, the calling convention passes it in {reg}"
  let mut block? := funcOp.getFunctionBody!.getFirstBlock! ctx.raw
  while let some block := block? do
    block? := block.getNextBlock! ctx.raw
    let some ret := block.getLastOp! ctx.raw | continue
    if ret.getOpType! ctx.raw != .riscv_cf .return then continue
    let operands := ret.getOperands! ctx.raw
    for h : i in [0:operands.size] do
      let value := operands[i]
      if let .preallocated r ← allocationState ctx value (aRegister i) s!"result {i}" then
        -- Only result 1 can be in a0 here (result 0 in a0 is `inTarget`). It is overwritten by the
        -- copy of result 0 into a0, unless result 0 also is in a0, e.g. (return %a, %a).
        if r == aRegister 0 && operands[0]? != some value then
          throw s!"illegal register allocation of function results: result {i} cannot be returned \
            from {r}, the copy of result 0 into it overwrites it"

/-! ## Rewrite patterns
-/

/-- `precolourArguments` as a rewrite pattern on function ops with a body. -/
def precolourArgumentsPattern : RewritePattern OpCode := fun rewriter op _ => do
  let some funcOp := FunctionOp.of? op rewriter.ctx.raw | return rewriter
  let some _ := funcOp.getEntryBlock? | return rewriter
  if funcOp.getArgumentTypes.zipIdx.all (fun (t, i) => t == .registerType (aRegister i)) then
    return rewriter
  let ctx ← (precolourArguments rewriter.ctx op).toOption
  return { rewriter with ctx, hasDoneAction := true }

/-- `precolourReturn` as a rewrite pattern on `riscv_cf.return`. -/
def precolourReturnPattern : RewritePattern OpCode := fun rewriter op _ => do
  if op.getOpType! rewriter.ctx.raw != .riscv_cf .return then return rewriter
  let operands := op.getOperands! rewriter.ctx.raw
  if operands.zipIdx.all (fun (v, i) => (v.getType! rewriter.ctx.raw).val == .registerType (aRegister i)) then
    return rewriter
  let ctx ← (precolourReturn rewriter.ctx op).toOption
  return { rewriter with ctx, hasDoneAction := true }

def RegisterPrecolouringPass.impl (ctx : WfIRContext OpCode) (op : OperationPtr)
    (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) := do
  for func in collectNestedFunctions ctx.raw op do
    checkPrecolourable ctx func
  let pattern := RewritePattern.GreedyRewritePattern #[precolourArgumentsPattern, precolourReturnPattern]
  match pattern.applyInContext ctx op with
  | none => throw "Error while applying register-precolouring-riscv64"
  | some ctx => pure ctx

public def RegisterPrecolouringPass : Pass OpCode :=
  { name := "register-precolouring-riscv64"
    description := "Pin RV64 function arguments to a0-a7 and return values to a0-a1 through move copies, before register allocation."
    run := fun _ => RegisterPrecolouringPass.impl }

end Veir
