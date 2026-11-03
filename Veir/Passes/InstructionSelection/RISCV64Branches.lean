module

public import Veir.Pass
import Veir.Passes.Matching
import Veir.PatternRewriter.Puddle.Builders
import Veir.PatternRewriter.Puddle.Execution
import Std

namespace Veir

/-!
  # Selecting gMIR branches for RISC-V

  The pass has a pure core, `convertModule`, written with folds over lists so
  that it can be reasoned about, and a thin `IO` wrapper around it.

  It works in two phases. First every `gmir.g_br` and `gmir.g_brcond` is replaced
  by a RISC-V branch whose operands are cast to registers, and every
  `llvm.unreachable` by `riscv_cf.unreachable`. A `g_brcond` on a `g_icmp`
  becomes a compare-and-branch such as `riscv_cf.blt`, as in LLVM's
  `RISCVInstructionSelector::selectBRCOND`, and any other one a `riscv_cf.bnez`.
  Then the arguments of every block that is branched to become registers, with
  a cast back to their original type at the start of the block.

  A branch is left alone, together with the blocks it targets, when its
  operands do not fit a register or when a target is also reached by a terminator
  the pass does not rewrite. In strict mode, the default, the pass then
  fails; with `strict=false` the branch survives alongside the lowered ones.
-/

/-- Whether a value of type `type` fits into a register without losing information. -/
def fitsRegister (type : TypeAttr) : Bool :=
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

/--
  Append to `regs` a register holding `operand`: a cast of it to a register inserted at `ip`, or
  `x0` for `none`.
-/
def regOf (ip : InsertPoint) (acc : WfIRContext OpCode × Array ValuePtr)
    (operand : Option ValuePtr) : Except String (WfIRContext OpCode × Array ValuePtr) := do
  let (ctx, regs) := acc
  match operand with
  | some operand =>
    let (ctx, casts) ← castToReg ip (ctx, #[]) operand
    return (ctx, regs.push (casts[0]!.getResult 0))
  | none =>
    let some (ctx, x0) := WfRewriter.createOp! ctx Rv64.get_register
      #[(RegisterType.mk (some 0) : TypeAttr)] #[] #[] #[] () ip
      | throw "isel-br-riscv64: cannot create x0"
    return (ctx, regs.push (x0.getResult 0))

/-- A conditional RISC-V branch. All of them take `RISCVBrProperties`. -/
abbrev CondBranch := { op : Riscv_Cf // Riscv_Cf.propertiesOf op = RISCVBrProperties }

/--
  The RISC-V branch that takes its first successor when `icmp pred lhs rhs` holds, with its two
  operands, where `none` is `x0`, as LLVM's `getOperandsForBranch`. `rhsConstant` is the value of
  `rhs` if it is a constant. A comparison against `-1` or `1` that is one against `0` compares
  with `x0` instead, and `sgt`, `sle`, `ugt` and `ule` swap the operands.
-/
def compareBranch (pred : Data.LLVM.IntPred) (lhs rhs : ValuePtr) (rhsConstant : Option Int) :
    CondBranch × Option ValuePtr × Option ValuePtr :=
  match pred, rhsConstant with
  -- `x > -1` is `x >= 0`.
  | .sgt, some (-1) => (⟨.bge, rfl⟩, some lhs, none)
  -- `x < 1` is `0 >= x`.
  | .slt, some 1 => (⟨.bge, rfl⟩, none, some lhs)
  | .eq, _ => (⟨.beq, rfl⟩, some lhs, some rhs)
  | .ne, _ => (⟨.bne, rfl⟩, some lhs, some rhs)
  | .slt, _ => (⟨.blt, rfl⟩, some lhs, some rhs)
  | .sge, _ => (⟨.bge, rfl⟩, some lhs, some rhs)
  | .ult, _ => (⟨.bltu, rfl⟩, some lhs, some rhs)
  | .uge, _ => (⟨.bgeu, rfl⟩, some lhs, some rhs)
  | .sgt, _ => (⟨.blt, rfl⟩, some rhs, some lhs)
  | .sle, _ => (⟨.bge, rfl⟩, some rhs, some lhs)
  | .ugt, _ => (⟨.bltu, rfl⟩, some rhs, some lhs)
  | .ule, _ => (⟨.bgeu, rfl⟩, some rhs, some lhs)

/-- Whether a value of type `type` fills a register, so that comparing registers compares values. -/
def fillsRegister (type : TypeAttr) : Bool :=
  match type.val with
  | .integerType intType => intType.bitwidth = 64
  | .llvmPointerType _ => true
  | _ => false

/--
  Match the branch condition `cond` against `g_icmp pred lhs rhs`, and return the
  compare-and-branch that replaces it. The operands must fill a register, as they do once the
  `g_icmp` is legal.
-/
def matchCompare (ctx : IRContext OpCode) (cond : ValuePtr) :
    Option (CondBranch × Option ValuePtr × Option ValuePtr) := do
  let .opResult icmp := cond | none
  let (operands, props) ← matchOp icmp.op ctx GMIR.g_icmp 2
  guard (fillsRegister (operands[0]!.getType! ctx))
  return compareBranch props.predicate operands[0]! operands[1]!
    (matchGConstantIntVal operands[1]! ctx)

/-- Whether `op` is a branch the pass rewrites, or a RISC-V branch that is already lowered. -/
def isLoweredBranch (ctx : WfIRContext OpCode) (op : OperationPtr) : Bool :=
  match op.getOpType! ctx.raw with
  | .gmir .g_br | .gmir .g_brcond | .riscv_cf _ => true
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
  Remove from `convertible` the targets of every `g_br` and `g_brcond`
  among `ops` that has a target outside of it. Such a branch is left alone and
  keeps passing values of their original types, so none of its targets may be
  converted. Removing a block can leave another branch alone, so this repeats
  until nothing changes, at most `fuel` times.
-/
def dropTargetsOfUnlowered (ctx : WfIRContext OpCode) (ops : List OperationPtr) :
    Nat → List BlockPtr → List BlockPtr
  | 0, convertible => convertible
  | fuel + 1, convertible =>
    let convertibleSet := Std.HashSet.ofList convertible
    let dropped := ops.flatMap fun op =>
      let opType := op.getOpType! ctx
      let targets := (op.getSuccessors! ctx.raw).toList
      if (opType = OpCode.gmir .g_br || opType = OpCode.gmir .g_brcond) &&
          !targets.all convertibleSet.contains then targets else []
    if dropped.any convertibleSet.contains then
      let droppedSet := Std.HashSet.ofList dropped
      dropTargetsOfUnlowered ctx ops fuel (convertible.filter (!droppedSet.contains ·))
    else
      convertible

/-- `llvm.unreachable` -> `riscv_cf.unreachable`. -/
def unreachable_pattern : Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let _ ← Puddle.MatchProg.root (.llvm .unreachable) #[] #[]
      return ())
    (fun () => do
      let _ ← Puddle.CreateProg.operation (.riscv_cf .unreachable) #[] #[]
      return ())
    (fun () => ⟨#[]⟩)

/--
  Replace the terminator `op` by its RISC-V counterpart if it is a `g_br`,
  a `g_brcond` or an `llvm.unreachable`, and leave any other operation
  alone. The operands are cast to registers in front of the new branch. A
  branch to a block that cannot be converted is left alone as well.
-/
def convertBranch (convertible : BlockPtr → Bool) (ctx : WfIRContext OpCode) (op : OperationPtr)
    : Except String (WfIRContext OpCode) := do
  let opType := op.getOpType! ctx
  if opType = OpCode.llvm .unreachable then
    /- Apply the pattern directly rather than through the greedy driver, which would also erase
       trivially dead operations elsewhere. -/
    let some (ctx, some (newOps, _)) := unreachable_pattern.interpret ctx op
      | throw "isel-br-riscv64: cannot create riscv_cf.unreachable"
    let ctx := newOps.foldl (fun ctx newOp => WfRewriter.insertOp! ctx newOp (InsertPoint.before op))
      ctx
    return WfRewriter.eraseOp! ctx op
  if opType != OpCode.gmir .g_br && opType != OpCode.gmir .g_brcond then
    return ctx
  if !(op.getSuccessors! ctx.raw).all convertible then
    return ctx

  let ip := InsertPoint.before op
  let operands := (List.range (op.getNumOperands! ctx.raw)).map (op.getOperand! ctx.raw ·)
  let successors := op.getSuccessors! ctx.raw
  -- Read `ctx` before the casts: any later read makes the first cast copy the whole context.
  let condProps := op.getProperties! ctx.raw GMIR.g_brcond
  let compare := if opType = OpCode.gmir .g_brcond then matchCompare ctx.raw operands[0]! else none
  -- A compare-and-branch takes the two compared values in place of the condition.
  let operands := match compare with
    | some (_, lhs, rhs) => lhs :: rhs :: (operands.drop 1).map some
    | none => operands.map some
  let (ctx', regs) ← operands.foldlM (regOf ip) (ctx, #[])

  let ctx' ←
    if opType = OpCode.gmir .g_br then do
      let some (ctx', _) := WfRewriter.createOp! ctx' Riscv_Cf.branch #[] regs
        #[successors[0]!] #[] default ip
        | throw "isel-br-riscv64: cannot create riscv_cf.branch"
      pure ctx'
    else do
      let segments := condProps.operandSegmentSizes
      let (branch, segments) : CondBranch × DenseArrayAttr := match compare with
        | some (branch, _, _) => (branch, { segments with values := #[1] ++ segments.values })
        | none => (⟨.bnez, rfl⟩, segments)
      let props : RISCVBrProperties := ⟨segments⟩
      let some (ctx', _) := WfRewriter.createOp! ctx' branch.val #[] regs
        successors #[] (cast branch.property.symm props) ip
        | throw "isel-br-riscv64: cannot create a conditional riscv_cf branch"
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
  let blocked := Std.HashSet.ofList (blockedTargets ctx)
  -- Each round that changes something removes a block, so this many suffice.
  let convertible := dropTargetsOfUnlowered ctx ops (blocks.length + 1)
    (blocks.filter fun block => !blocked.contains block && isConvertible ctx block)
  -- As a set, so that each lookup below does not walk the list.
  let convertible := Std.HashSet.ofList convertible
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
        throw "isel-br-riscv64: cannot lower a branch other than g_br or g_brcond"
    for o in ctx.raw.operations.keys do
      let opType := o.getOpType! ctx.raw
      if opType = OpCode.gmir .g_br || opType = OpCode.gmir .g_brcond then
        throw "isel-br-riscv64: a branch operand does not fit a register"
  return ctx

public def IselBrRISCV64 : Pass OpCode :=
  { name := "isel-br-riscv64"
    description :=
      "Select gMIR branch instructions for RISCV 64."
    options := .ofList [
      ("strict", { description := "Fail if not all branches could be lowered.",
                   defaultValue := true })]
    run := fun options => ISelBrPass.impl ((options.get? "strict").getD true) }
