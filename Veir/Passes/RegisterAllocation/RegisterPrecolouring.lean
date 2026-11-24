module

public import Veir.Pass
import Veir.Passes.RegisterAllocation.Helper
import Veir.Rewriter.WfRewriter

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

/-- The ABI registers `a<i>` (`x(10+i)`) that hold function arguments and return values. -/
def aRegister (i : Nat) : RegisterType := { cls := .int, index := some (10 + i) }

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
Pin each argument of the entry block to its physical register `a<i>` (`x(10+i)`). Insert a `mv` at the
start of the entry block to copy the argument into a fresh unassigned value, which takes over all of its uses.
-/
def precolourArguments (ctx : WfIRContext OpCode) (entry : BlockPtr) :
    Except String (WfIRContext OpCode) := do
  let mut ctx := ctx
  -- Copies are inserted at the start of the block, so walk the arguments backwards to
  -- leave the copies in argument order.
  for i in (List.range (entry.getNumArguments! ctx.raw)).reverse do
    let arg : BlockArgumentPtr := { block := entry, index := i }
    let arg' : ValuePtr := .blockArgument arg
    let reg := aRegister i
    match ← allocationState ctx arg' reg s!"argument {i}" with
    | .inTarget => continue
    | .preallocated r => throw s!"precolouring cannot move argument {i} of type {r} into {reg}"
    | .unallocated => pure ()
    ctx := WfRewriter.setType! ctx arg' reg
    if (arg'.getFirstUse! ctx.raw).isNone then continue
    let some (ctx', copy) := WfRewriter.createOp! ctx Riscv.mv #[RegisterType.mk] #[] #[] #[] ()
        (some (InsertPoint.atStart! entry ctx.raw))
      | throw s!"precolouring could not copy argument {i}"
    let ctx' := WfRewriter.replaceValue! ctx' arg' (copy.getResult 0)
    ctx := WfRewriter.pushOperand! ctx' copy arg'
  return ctx

/--
Copy each result of the function into its return value, right before the `riscv_cf.return`
that ends `entry`:
- A return value is the operand of `riscv_cf.return`, and must be in `a<i>` (`aRegister i`).
- A result is the value the function computes. It may have a preallocated physical register,
  and is copied into its return value.

The copies run sequentially, so a copy must not overwrite a result that a later copy still
reads:
- An unassigned result is safe: the physical renaming pass (later) excludes `a0`/`a1`.
- A preallocated result can be overwritten. With at most two results, the only case is
  result 1 preallocated to `a0`: the copy of result 0 into `a0` runs first, e.g.
  `return %b, %a` with `%a` in `a0`. This case is rejected.
-/
def precolourResults (ctx : WfIRContext OpCode) (entry : BlockPtr) :
    Except String (WfIRContext OpCode) := do
  let some ret := entry.getLastOp! ctx.raw | return ctx
  if ret.getOpType! ctx.raw != .riscv_cf .return then return ctx
  let operands := ret.getOperands! ctx.raw
  if operands.size > maxRegisterResults then
    throw s!"precolouring supports at most {maxRegisterResults} function results"
  let mut ctx := ctx
  for h : i in [0:operands.size] do
    let value := operands[i]
    let reg := aRegister i
    match ← allocationState ctx value reg s!"result {i}" with
    | .inTarget => continue
    | .preallocated r =>
      -- Result 0 in `a0` is `inTarget`, so this only fires for result 1.
      if r == aRegister 0 then
        throw s!"precolouring cannot return result {i} from a0: the copy of result 0 into a0 overwrites it"
    | .unallocated => pure ()
    let some (ctx', copy) := WfRewriter.createOp! ctx Riscv.mv #[reg] #[value] #[] #[] ()
        (some (.before ret))
      | throw s!"precolouring could not copy result {i} into its return value"
    ctx := WfRewriter.replaceOperand! ctx' ⟨ret, i⟩ (copy.getResult 0)
  return ctx

/--
Rewrite the signature of the function whose entry block is `entry` so that its argument
types match those of the entry block's arguments.
-/
def updateSignature (ctx : WfIRContext OpCode) (entry : BlockPtr) :
    Except String (WfIRContext OpCode) := do
  let some func := (entry.getParent! ctx.raw).bind (·.getParent! ctx.raw)
    | throw "precolouring expects the entry block to belong to a function"
  let some funcOp := FunctionOp.of? func ctx.raw
    | throw "precolouring expects the entry block to belong to a function"
  let inputs := (Array.range (entry.getNumArguments! ctx.raw)).map fun i =>
    ((ValuePtr.blockArgument { block := entry, index := i }).getType! ctx.raw).val
  return FunctionOp.setFunctionType! ctx funcOp inputs funcOp.getResultTypes

/-- Precolour the arguments and results of the function whose entry block is `entry`. -/
def precolourFunction (ctx : WfIRContext OpCode) (entry : BlockPtr) :
    Except String (WfIRContext OpCode) := do
  let ctx ← precolourArguments ctx entry
  let ctx ← precolourResults ctx entry
  updateSignature ctx entry

def RegisterPrecolouringPass.impl (ctx : WfIRContext OpCode) (op : OperationPtr)
    (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) := do
  let entries ← allocatableBlocks ctx op
  let mut ctx := ctx
  for entry in entries do
    ctx ← precolourFunction ctx entry
  return ctx

public def RegisterPrecolouringPass : Pass OpCode :=
  { name := "register-precolouring-riscv64"
    description := "Pin RV64 function arguments to a0-a7 and return values to a0-a1 through move copies, before register allocation."
    run := fun _ => RegisterPrecolouringPass.impl }

end Veir
