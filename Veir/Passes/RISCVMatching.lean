import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching

/-! This file contains helper functions to match RISCV operations. -/

namespace Veir.RISCV

def matchRiscvBinop (oc : Riscv) (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr) := do
  let (op, _) ← matchOp op ctx (.riscv oc) 2
  return (op[0]!, op[1]!)

def matchAdd := matchRiscvBinop .add

def matchLi (val : ValuePtr) (ctx : IRContext OpCode) : Option (propertiesOf (.riscv .li)) := do
  let op ← val.getDefiningOp! ctx
  let (_, properties) ← matchOp op ctx (.riscv .li) 0
  return properties

/-- Match a value defined by `riscv.zextw`, returning its source operand. -/
def matchZextw (val : ValuePtr) (ctx : IRContext OpCode) : Option ValuePtr := do
  let op ← val.getDefiningOp! ctx
  let (operands, _) ← matchOp op ctx (.riscv .zextw) 1
  return operands[0]!

/-! ## Facts derived from a successful `matchRiscvBinop` -/

/-- A successful `matchRiscvBinop` implies the matched operation has one result. -/
theorem matchRiscvBinop_getNumResults {oc : Riscv} {op : OperationPtr} {ctx : IRContext OpCode}
    {r : ValuePtr × ValuePtr} (h : matchRiscvBinop oc op ctx = some r) :
    op.getNumResults! ctx = 1 := by
  unfold matchRiscvBinop at h
  obtain ⟨a, ha, _⟩ := Option.bind_eq_some_iff.mp h
  exact matchOp_getNumResults ha

/-- The first operand returned by a successful `matchRiscvBinop` is in bounds. This is what
    discharges the `createOp` operand obligation in the corresponding combine. -/
theorem matchRiscvBinop_reg_inBounds {oc : Riscv} {op : OperationPtr} {ctx : WfIRContext OpCode}
    {reg rhs : ValuePtr} (h : matchRiscvBinop oc op ctx = some (reg, rhs)) :
    reg.InBounds ctx.raw := by
  unfold matchRiscvBinop at h
  obtain ⟨⟨ops, props⟩, hmatch, hres⟩ := Option.bind_eq_some_iff.mp h
  have hin : op.InBounds ctx.raw := matchOp_inBounds (by omega) hmatch
  have hnum : op.getNumOperands! ctx.raw = 2 := matchOp_getNumOperands hmatch
  have hops : ops = op.getOperands! ctx.raw := matchOp_operands hmatch
  have hreg : reg = op.getOperand! ctx.raw 0 := by
    have h2 := Option.some.inj hres
    have hr : reg = ops[0]! := (congrArg Prod.fst h2).symm
    rw [hr, hops, OperationPtr.getOperands!.getElem!_eq_getOperand!]
  rw [hreg]
  exact OperationPtr.getOperands!_inBounds ctx.wellFormed.inBounds hin
    (OperationPtr.getOperands!.mem_getOperand (by omega))
