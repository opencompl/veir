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

/- `getEffects` reports the effects themselves, and inspects properties. -/

#guard OpCode.getEffects (.llvm .load) (default : LoadProperties) == #[.read]
#guard OpCode.getEffects (.llvm .load) volatileLoadProperties == #[.read, .write]

#guard OpCode.getEffects (.llvm .store) (default : StoreProperties) == #[.write]
#guard OpCode.getEffects (.llvm .store) volatileStoreProperties == #[.write, .read]

#guard OpCode.getEffects (.arith .addi) (default : ArithIntegerOverflowFlagsProperties) == #[]

/- RISC-V models volatility the same way, on its own load and store opcodes. -/

#guard OpCode.getEffects (.riscv .lw) (default : RISCVMemProperties) == #[.read]
#guard OpCode.getEffects (.riscv .lw) volatileMemProperties == #[.read, .write]

#guard OpCode.getEffects (.riscv .sw) (default : RISCVMemProperties) == #[.write]
#guard OpCode.getEffects (.riscv .sw) volatileMemProperties == #[.write, .read]

#guard OpCode.getEffects (.riscv .add) (default : Unit) == #[]

/-
  A call is conservative in both directions: we have no interprocedural effect
  analysis, so the callee may do anything. Upstream reaches the same answer by
  a different route, as `func.call` implements no memory effect interface at
  all and so has unknown effects.
-/

#guard OpCode.getEffects (.func .call) (default : FuncCallProperties) == #[.read, .write]

/- The derived queries distinguish reads from writes. -/

#guard HasOpInfo.readsMemory (OpCode.llvm .load) (default : LoadProperties)
#guard !(HasOpInfo.writesMemory (OpCode.llvm .load) (default : LoadProperties))
#guard HasOpInfo.writesMemory (OpCode.llvm .load) volatileLoadProperties

#guard HasOpInfo.writesMemory (OpCode.llvm .store) (default : StoreProperties)
#guard !(HasOpInfo.readsMemory (OpCode.llvm .store) (default : StoreProperties))
#guard HasOpInfo.readsMemory (OpCode.llvm .store) volatileStoreProperties

#guard hasEffect (OpCode.getEffects (.llvm .load) volatileLoadProperties) .write
#guard !(hasEffect (OpCode.getEffects (.llvm .load) (default : LoadProperties)) .write)

#guard !(isMemoryEffectFree (OpCode.getEffects (.llvm .load) (default : LoadProperties)))
#guard isMemoryEffectFree
  (OpCode.getEffects (.arith .addi) (default : ArithIntegerOverflowFlagsProperties))

/- Operations carrying regions are conservatively treated as reading and writing. -/

/-- A `builtin.module` op, which always carries a single region. -/
private def moduleWithRegion : OperationPtr × IRContext OpCode :=
  let (ctx, moduleOp) := WfIRContext.create! OpCode
  (moduleOp, ctx.raw)

#guard moduleWithRegion.1.readsMemory moduleWithRegion.2
#guard moduleWithRegion.1.writesMemory moduleWithRegion.2
