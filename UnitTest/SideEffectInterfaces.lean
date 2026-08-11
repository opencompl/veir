import Veir.GlobalOpInfo
import Veir.Interfaces.SideEffectInterfaces
import Veir.Rewriter.WfRewriter.Basic

open Veir

private def volatileLoadProperties : LoadProperties :=
  { (default : LoadProperties) with volatile_ := true }

private def volatileStoreProperties : StoreProperties :=
  { (default : StoreProperties) with volatile_ := true }

private def volatileMemProperties : RISCVMemProperties :=
  { (default : RISCVMemProperties) with volatile_ := true }

#guard OpCode.getEffects (.llvm .load) (default : LoadProperties) == .read
#guard OpCode.getEffects (.llvm .load) volatileLoadProperties == .readWrite

#guard OpCode.getEffects (.llvm .store) (default : StoreProperties) == .write
#guard OpCode.getEffects (.llvm .store) volatileStoreProperties == .readWrite

#guard OpCode.getEffects (.arith .addi) (default : ArithIntegerOverflowFlagsProperties) == .none

/- RISC-V models volatility the same way, on its own load and store opcodes. -/

#guard OpCode.getEffects (.riscv .lw) (default : RISCVMemProperties) == .read
#guard OpCode.getEffects (.riscv .lw) volatileMemProperties == .readWrite

#guard OpCode.getEffects (.riscv .sw) (default : RISCVMemProperties) == .write
#guard OpCode.getEffects (.riscv .sw) volatileMemProperties == .readWrite

#guard OpCode.getEffects (.riscv .add) (default : Unit) == .none

/-
  A call is conservative in both directions: we have no interprocedural effect
  analysis, so the callee may do anything. Upstream reaches the same answer by
  a different route, as `func.call` implements no memory effect interface at
  all and so has unknown effects.
-/

#guard OpCode.getEffects (.func .call) (default : FuncCallProperties) == .readWrite

/- Operations carrying regions are conservatively treated as reading and writing. -/

/-- A `builtin.module` op, which always carries a single region. -/
private def moduleWithRegion : OperationPtr × IRContext OpCode :=
  let (ctx, moduleOp) := WfIRContext.create! OpCode
  (moduleOp, ctx.raw)

#guard moduleWithRegion.1.getEffects moduleWithRegion.2 == .readWrite
