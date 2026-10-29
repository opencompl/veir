module

public import Veir.Interpreter
public import Veir.Passes.InstructionSelection.Branches.Casts

public section

/-!
# What the branch lowering does to a module

`BranchLowering ctx ctx'` describes the module `ctx'` that the lowering of gMIR
branches makes of `ctx`, without reference to how the rewriter builds it. The
proof that the lowering refines the module only uses this description, and the
proof about the pass only has to establish it.

Every `g_br` and `g_brcond` is replaced by operations that put registers in
front of a RISC-V branch: casts of its operands, and for a compare-and-branch
casts of the compared values or `x0` in place of the condition. The arguments of
every block that is branched to are registers, and a cast at the start of the
block gives each its original type. Everything else is unchanged, except that a
use of such an argument is a use of its cast.
-/

namespace Veir

/-- What replaces the condition of a `g_brcond`: a compare-and-branch and the values it compares. -/
abbrev Compare := CondBranch × Option ValuePtr × Option ValuePtr

/-- The operations that stand for `op`, given the operations that put registers in front of it. -/
@[expose]
def lowerOp (ctx : IRContext OpCode) (compare : OperationPtr → Option Compare)
    (regOp : OperationPtr → Nat → OperationPtr) (newBranch : OperationPtr → OperationPtr)
    (op : OperationPtr) : List OperationPtr :=
  if op.IsGmirBranch ctx then
    (List.range (regOperands ctx op (compare op)).length).map (regOp op) ++ [newBranch op]
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
  /-- The compare-and-branch that replaces a `g_brcond` and the values it compares, if any. -/
  compare : OperationPtr → Option Compare
  /-- The `g_icmp` whose result a `g_brcond` that becomes a compare-and-branch tests. -/
  icmpOf : OperationPtr → OperationPtr
  /-- The value of the constant that such a `g_icmp` compares with, if it is one. -/
  constantOf : OperationPtr → Option Int
  /-- The operations that put the registers in front of the branch that replaces a branch. -/
  regOp : OperationPtr → Nat → OperationPtr
  /-- The RISC-V branch that replaces a branch. -/
  newBranch : OperationPtr → OperationPtr

  -- Blocks and regions
  blockIn {block : BlockPtr} : block.InBounds ctx.raw → block.InBounds ctx'.raw
  numArguments {block : BlockPtr} : block.InBounds ctx.raw →
    block.getNumArguments! ctx'.raw = block.getNumArguments! ctx.raw
  operationList {block : BlockPtr} (hBlock : block.InBounds ctx.raw) :
    (block.operationList ctx'.raw ctx'.wellFormed (blockIn hBlock)).toList =
      (if converted block then
        (List.range (block.getNumArguments! ctx.raw)).map
          (fun i => argCast (block.getArgument i))
      else []) ++
      (block.operationList ctx.raw ctx.wellFormed hBlock).toList.flatMap
        (lowerOp ctx.raw compare regOp newBranch)
  regionIn {region : RegionPtr} : region.InBounds ctx.raw → region.InBounds ctx'.raw
  firstBlock {region : RegionPtr} : region.InBounds ctx.raw →
    region.getFirstBlock! ctx'.raw = region.getFirstBlock! ctx.raw
  /-- The arguments of an entry block are those of the enclosing operation. -/
  entryNotConverted {region : RegionPtr} {block : BlockPtr} : region.InBounds ctx.raw →
    region.getFirstBlock! ctx.raw = some block → converted block = false

  -- Block arguments
  argTypeConverted {block : BlockPtr} {i : Nat} : block.InBounds ctx.raw → converted block →
    i < block.getNumArguments! ctx.raw →
    (block.getArgument i : ValuePtr).getType! ctx'.raw = (RegisterType.mk : TypeAttr) ∧
    roundTrips ((block.getArgument i : ValuePtr).getType! ctx.raw)
  argTypeOther {block : BlockPtr} {i : Nat} : block.InBounds ctx.raw → converted block = false →
    i < block.getNumArguments! ctx.raw →
    (block.getArgument i : ValuePtr).getType! ctx'.raw =
      (block.getArgument i : ValuePtr).getType! ctx.raw
  argCastSpec {arg : BlockArgumentPtr} : arg.InBounds ctx.raw → converted arg.block →
    (argCast arg).InBounds ctx'.raw ∧
    (∀ result : OpResultPtr, result.InBounds ctx.raw → result.op ≠ argCast arg) ∧
    (argCast arg).getOpType! ctx'.raw = .builtin .unrealized_conversion_cast ∧
    (argCast arg).getResultTypes! ctx'.raw = #[(ValuePtr.blockArgument arg).getType! ctx.raw] ∧
    (argCast arg).getOperands! ctx'.raw = #[.blockArgument arg]
  argCastInj {arg₁ arg₂ : BlockArgumentPtr} : arg₁.InBounds ctx.raw → arg₂.InBounds ctx.raw →
    converted arg₁.block → converted arg₂.block → argCast arg₁ = argCast arg₂ → arg₁ = arg₂

  -- Operations other than the two branches
  opSpec {op : OperationPtr} : op.InBounds ctx.raw → ¬ op.IsGmirBranch ctx.raw →
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
  opSuccessors {op : OperationPtr} : op.InBounds ctx.raw → ¬ op.IsGmirBranch ctx.raw →
    op.getSuccessors! ctx.raw = #[] ∧ op.getSuccessors! ctx'.raw = #[]

  -- The two branches
  branchNumResults {op : OperationPtr} : op.InBounds ctx.raw → op.IsGmirBranch ctx.raw →
    op.getNumResults! ctx.raw = 0
  branchSuccessorConverted {op : OperationPtr} {block : BlockPtr} : op.InBounds ctx.raw →
    op.IsGmirBranch ctx.raw → block ∈ op.getSuccessors! ctx.raw → converted block
  /-- The operands of a branch fit a register. -/
  operandRoundTrips {op : OperationPtr} {i : Nat} : op.InBounds ctx.raw →
    op.IsGmirBranch ctx.raw → i < op.getNumOperands! ctx.raw →
    roundTrips ((op.getOperand! ctx.raw i).getType! ctx.raw)
  /-- A new operation in front of the new branch. -/
  regOpSpec {op : OperationPtr} {i : Nat} : op.InBounds ctx.raw →
    op.IsGmirBranch ctx.raw → i < (regOperands ctx.raw op (compare op)).length →
    (regOp op i).InBounds ctx'.raw ∧
    (∀ result : OpResultPtr, result.InBounds ctx.raw → result.op ≠ regOp op i) ∧
    (∀ arg : BlockArgumentPtr, arg.InBounds ctx.raw → converted arg.block →
      argCast arg ≠ regOp op i)
  /-- The cast in front of the new branch of a value to a register. -/
  regOpCast {op : OperationPtr} {i : Nat} {value : ValuePtr} : op.InBounds ctx.raw →
    op.IsGmirBranch ctx.raw → (regOperands ctx.raw op (compare op))[i]? = some (some value) →
    (regOp op i).getOpType! ctx'.raw = .builtin .unrealized_conversion_cast ∧
    (regOp op i).getResultTypes! ctx'.raw = #[(RegisterType.mk : TypeAttr)] ∧
    (regOp op i).getOperands! ctx'.raw = #[lowerValue converted argCast value]
  /-- The operation in front of the new branch that reads `x0`. -/
  regOpX0 {op : OperationPtr} {i : Nat} : op.InBounds ctx.raw →
    op.IsGmirBranch ctx.raw → (regOperands ctx.raw op (compare op))[i]? = some none →
    (regOp op i).getOpType! ctx'.raw = .rv64 .get_register ∧
    (regOp op i).getResultTypes! ctx'.raw = #[(RegisterType.mk (some 0) : TypeAttr)] ∧
    (regOp op i).getOperands! ctx'.raw = #[]
  regOpInj {op : OperationPtr} {i j : Nat} : op.InBounds ctx.raw →
    op.IsGmirBranch ctx.raw → i < (regOperands ctx.raw op (compare op)).length →
    j < (regOperands ctx.raw op (compare op)).length → regOp op i = regOp op j → i = j
  newBranchSpec {op : OperationPtr} : op.InBounds ctx.raw → op.IsGmirBranch ctx.raw →
    (newBranch op).InBounds ctx'.raw ∧
    (newBranch op).getNumResults! ctx'.raw = 0 ∧
    (newBranch op).getSuccessors! ctx'.raw = op.getSuccessors! ctx.raw ∧
    (newBranch op).getOperands! ctx'.raw =
      (Array.range (regOperands ctx.raw op (compare op)).length).map
        (fun i => ((regOp op i).getResult 0 : ValuePtr))
  newBranchBr {op : OperationPtr} : op.InBounds ctx.raw → op.getOpType! ctx.raw = .gmir .g_br →
    compare op = none ∧ (newBranch op).getOpType! ctx'.raw = .riscv_cf .branch
  newBranchBnez {op : OperationPtr} : op.InBounds ctx.raw →
    op.getOpType! ctx.raw = .gmir .g_brcond → compare op = none →
    (newBranch op).getOpType! ctx'.raw = .riscv_cf .bnez ∧
    ((newBranch op).getProperties! ctx'.raw (OpCode.riscv_cf .bnez)).operandSegmentSizes =
      (op.getProperties! ctx.raw (OpCode.gmir .g_brcond)).operandSegmentSizes
  newBranchCompare {op : OperationPtr} {branch : CondBranch} {lhs rhs : Option ValuePtr} :
    op.InBounds ctx.raw → compare op = some (branch, lhs, rhs) →
    (newBranch op).getOpType! ctx'.raw = .riscv_cf branch.val ∧
    ∃ segments : DenseArrayAttr,
      (newBranch op).getProperties! ctx'.raw (OpCode.riscv_cf branch.val) =
        cast branch.property.symm (⟨segments⟩ : RISCVBrProperties) ∧
      segments.values =
        #[1] ++ (op.getProperties! ctx.raw (OpCode.gmir .g_brcond)).operandSegmentSizes.values

  -- The compares
  /--
    A `g_brcond` that becomes a compare-and-branch tests the result of a `g_icmp`
    of two values that fill a register, neither of which is that result, and the
    compare-and-branch is the one that `compareBranch` picks for the `g_icmp`.
  -/
  compareSpec {op : OperationPtr} {c : Compare} : op.InBounds ctx.raw → compare op = some c →
    op.getOpType! ctx.raw = .gmir .g_brcond ∧
    (icmpOf op).InBounds ctx.raw ∧
    (icmpOf op).getOpType! ctx.raw = .gmir .g_icmp ∧
    (icmpOf op).getNumResults! ctx.raw = 1 ∧
    op.getOperand! ctx.raw 0 = (icmpOf op).getResult 0 ∧
    (icmpOf op).getNumOperands! ctx.raw = 2 ∧
    (icmpOf op).getOperand! ctx.raw 0 ≠ (icmpOf op).getResult 0 ∧
    (icmpOf op).getOperand! ctx.raw 1 ≠ (icmpOf op).getResult 0 ∧
    fillsRegister (((icmpOf op).getOperand! ctx.raw 0).getType! ctx.raw) ∧
    compareBranch ((icmpOf op).getProperties! ctx.raw (OpCode.gmir .g_icmp)).predicate
      ((icmpOf op).getOperand! ctx.raw 0) ((icmpOf op).getOperand! ctx.raw 1) (constantOf op) = c
  /-- The constant that a `g_icmp` compares with is the value of a `g_constant`. -/
  constantSpec {op : OperationPtr} {c : Compare} {k : Int} : op.InBounds ctx.raw →
    compare op = some c → constantOf op = some k →
    ∃ (constant : OperationPtr) (type : TypeAttr) (t : IntegerType),
      (icmpOf op).getOperand! ctx.raw 1 = constant.getResult 0 ∧
      constant.InBounds ctx.raw ∧ constant.getOpType! ctx.raw = .gmir .g_constant ∧
      (constant.getResultTypes! ctx.raw)[0]? = some type ∧ type.val = .integerType t ∧
      k = (BitVec.ofInt t.bitwidth
        (constant.getProperties! ctx.raw (OpCode.gmir .g_constant)).value.value).toInt
  /-- The `g_icmp` comes right before the `g_brcond` in its block. -/
  compareAdjacent {op : OperationPtr} {c : Compare} {block : BlockPtr}
    (blockIn : block.InBounds ctx.raw) {pre post : List OperationPtr} : op.InBounds ctx.raw →
    compare op = some c →
    (block.operationList ctx.raw ctx.wellFormed blockIn).toList = pre ++ op :: post →
    pre.getLast? = some (icmpOf op)

end Veir
