module

public import Veir.Interpreter
public import Veir.Passes.InstructionSelection.RISCV64Branches

public section

/-!
# What the branch lowering does to a module

`BranchLowering ctx ctx'` describes the module `ctx'` that the lowering of LLVM
branches makes of `ctx`, without reference to how the rewriter builds it. The
proof that the lowering refines the module only uses this description, and the
proof about the pass only has to establish it.

Every `llvm.br` and `llvm.cond_br` is replaced by casts of its operands to
registers followed by a RISC-V branch. The arguments of every block that is
branched to are registers, and a cast at the start of the block gives each its
original type. Everything else is unchanged, except that a use of such an
argument is a use of its cast.
-/

namespace Veir

/-- `op` is one of the two LLVM branches that the lowering replaces. -/
@[expose]
def OperationPtr.IsLlvmBranch (op : OperationPtr) (ctx : IRContext OpCode) : Prop :=
  op.getOpType! ctx = .llvm .br ∨ op.getOpType! ctx = .llvm .cond_br

instance {op : OperationPtr} {ctx : IRContext OpCode} : Decidable (op.IsLlvmBranch ctx) := by
  unfold OperationPtr.IsLlvmBranch; infer_instance

/-- The operations that stand for `op`, given the casts of a branch and its replacement. -/
@[expose]
def lowerOp (ctx : IRContext OpCode) (operandCast : OperationPtr → Nat → OperationPtr)
    (newBranch : OperationPtr → OperationPtr) (op : OperationPtr) : List OperationPtr :=
  if op.IsLlvmBranch ctx then
    (List.range (op.getNumOperands! ctx)).map (operandCast op) ++ [newBranch op]
  else
    [op]

/-- The value that stands for `value`, given which blocks are converted and their casts. -/
@[expose]
def lowerValue (converted : BlockPtr → Bool) (argCast : BlockArgumentPtr → OperationPtr)
    (value : ValuePtr) : ValuePtr :=
  match value with
  | .blockArgument arg => if converted arg.block then (argCast arg).getResult 0 else value
  | .opResult _ => value

/-- `ctx'` is the branch lowering of `ctx`. -/
structure BranchLowering (ctx ctx' : WfIRContext OpCode) where
  /-- Whether the arguments of a block became registers. -/
  converted : BlockPtr → Bool
  /-- The cast at the start of a converted block that gives an argument its original type. -/
  argCast : BlockArgumentPtr → OperationPtr
  /-- The cast of an operand of a branch to a register. -/
  operandCast : OperationPtr → Nat → OperationPtr
  /-- The RISC-V branch that replaces a branch. -/
  newBranch : OperationPtr → OperationPtr

  -- Blocks and regions
  blockIn {block : BlockPtr} : block.InBounds ctx.raw → block.InBounds ctx'.raw
  numArguments {block : BlockPtr} : block.InBounds ctx.raw →
    block.getNumArguments! ctx'.raw = block.getNumArguments! ctx.raw
  operationList {block : BlockPtr} (hBlock : block.InBounds ctx.raw) :
    (block.operationList ctx'.raw ctx'.wellFormed (blockIn hBlock)).toList =
      (if converted block then
        (List.range (block.getNumArguments! ctx.raw)).reverse.map
          (fun i => argCast (block.getArgument i))
      else []) ++
      (block.operationList ctx.raw ctx.wellFormed hBlock).toList.flatMap
        (lowerOp ctx.raw operandCast newBranch)
  regionIn {region : RegionPtr} : region.InBounds ctx.raw → region.InBounds ctx'.raw
  firstBlock {region : RegionPtr} : region.InBounds ctx.raw →
    (region.get! ctx'.raw).firstBlock = (region.get! ctx.raw).firstBlock
  /-- The arguments of an entry block are those of the enclosing operation. -/
  entryNotConverted {region : RegionPtr} {block : BlockPtr} : region.InBounds ctx.raw →
    (region.get! ctx.raw).firstBlock = some block → converted block = false

  -- Block arguments
  argTypeConverted {block : BlockPtr} {i : Nat} : block.InBounds ctx.raw → converted block →
    i < block.getNumArguments! ctx.raw →
    (block.getArgument i : ValuePtr).getType! ctx'.raw = (RegisterType.mk : TypeAttr) ∧
    fitsRegister ((block.getArgument i : ValuePtr).getType! ctx.raw)
  argTypeOther {block : BlockPtr} {i : Nat} : block.InBounds ctx.raw → converted block = false →
    i < block.getNumArguments! ctx.raw →
    (block.getArgument i : ValuePtr).getType! ctx'.raw =
      (block.getArgument i : ValuePtr).getType! ctx.raw
  argCastSpec {arg : BlockArgumentPtr} : arg.InBounds ctx.raw → converted arg.block →
    (argCast arg).InBounds ctx'.raw ∧ ¬ (argCast arg).InBounds ctx.raw ∧
    (argCast arg).getOpType! ctx'.raw = .builtin .unrealized_conversion_cast ∧
    (argCast arg).getResultTypes! ctx'.raw = #[(ValuePtr.blockArgument arg).getType! ctx.raw] ∧
    (argCast arg).getOperands! ctx'.raw = #[.blockArgument arg]
  argCastInj {arg₁ arg₂ : BlockArgumentPtr} : arg₁.InBounds ctx.raw → arg₂.InBounds ctx.raw →
    converted arg₁.block → converted arg₂.block → argCast arg₁ = argCast arg₂ → arg₁ = arg₂

  -- Operations other than the two branches
  opSpec {op : OperationPtr} : op.InBounds ctx.raw → ¬ op.IsLlvmBranch ctx.raw →
    op.InBounds ctx'.raw ∧
    op.getOpType! ctx'.raw = op.getOpType! ctx.raw ∧
    (∀ {Dialect : Type} [HasOpInfo Dialect] [HasDialect OpCode Dialect] (opCode : Dialect),
      op.getProperties! ctx'.raw opCode = op.getProperties! ctx.raw opCode) ∧
    op.getResultTypes! ctx'.raw = op.getResultTypes! ctx.raw ∧
    op.getOperands! ctx'.raw = (op.getOperands! ctx.raw).map (lowerValue converted argCast) ∧
    op.getNumRegions! ctx'.raw = op.getNumRegions! ctx.raw ∧
    op.getRegion! ctx'.raw 0 = op.getRegion! ctx.raw 0 ∧
    op.getParentOp! ctx'.raw = op.getParentOp! ctx.raw
  /-- Only the two branches pass values to a block. -/
  opSuccessors {op : OperationPtr} : op.InBounds ctx.raw → ¬ op.IsLlvmBranch ctx.raw →
    op.getSuccessors! ctx.raw = #[] ∧ op.getSuccessors! ctx'.raw = #[]

  -- The two branches
  branchNumResults {op : OperationPtr} : op.InBounds ctx.raw → op.IsLlvmBranch ctx.raw →
    op.getNumResults! ctx.raw = 0
  branchSuccessorConverted {op : OperationPtr} {block : BlockPtr} : op.InBounds ctx.raw →
    op.IsLlvmBranch ctx.raw → block ∈ op.getSuccessors! ctx.raw → converted block
  operandCastSpec {op : OperationPtr} {i : Nat} : op.InBounds ctx.raw →
    op.IsLlvmBranch ctx.raw → i < op.getNumOperands! ctx.raw →
    (operandCast op i).InBounds ctx'.raw ∧ ¬ (operandCast op i).InBounds ctx.raw ∧
    (operandCast op i).getOpType! ctx'.raw = .builtin .unrealized_conversion_cast ∧
    (operandCast op i).getResultTypes! ctx'.raw = #[(RegisterType.mk : TypeAttr)] ∧
    (operandCast op i).getOperands! ctx'.raw =
      #[lowerValue converted argCast (op.getOperand! ctx.raw i)] ∧
    fitsRegister ((op.getOperand! ctx.raw i).getType! ctx.raw) ∧
    (∀ arg : BlockArgumentPtr, arg.InBounds ctx.raw → converted arg.block →
      argCast arg ≠ operandCast op i)
  operandCastInj {op : OperationPtr} {i j : Nat} : op.InBounds ctx.raw →
    op.IsLlvmBranch ctx.raw → i < op.getNumOperands! ctx.raw → j < op.getNumOperands! ctx.raw →
    operandCast op i = operandCast op j → i = j
  newBranchSpec {op : OperationPtr} : op.InBounds ctx.raw → op.IsLlvmBranch ctx.raw →
    (newBranch op).InBounds ctx'.raw ∧
    (newBranch op).getNumResults! ctx'.raw = 0 ∧
    (newBranch op).getSuccessors! ctx'.raw = op.getSuccessors! ctx.raw ∧
    (newBranch op).getOperands! ctx'.raw =
      (Array.range (op.getNumOperands! ctx.raw)).map
        (fun i => ((operandCast op i).getResult 0 : ValuePtr))
  newBranchBr {op : OperationPtr} : op.InBounds ctx.raw → op.getOpType! ctx.raw = .llvm .br →
    (newBranch op).getOpType! ctx'.raw = .riscv_cf .branch
  newBranchCondBr {op : OperationPtr} : op.InBounds ctx.raw →
    op.getOpType! ctx.raw = .llvm .cond_br →
    (newBranch op).getOpType! ctx'.raw = .riscv_cf .bnez ∧
    ((newBranch op).getProperties! ctx'.raw (OpCode.riscv_cf .bnez)).operandSegmentSizes =
      (op.getProperties! ctx.raw (OpCode.llvm .cond_br)).operandSegmentSizes

end Veir
