import Veir.GlobalOpInfo
import Veir.Interfaces.SideEffectInterfaces
import Veir.Rewriter.WfRewriter.Basic

open Veir

private def volatileLoadProperties : LoadProperties :=
  { (default : LoadProperties) with volatile_ := true }

private def volatileStoreProperties : StoreProperties :=
  { (default : StoreProperties) with volatile_ := true }

/- `getEffects` reports the effects themselves, and inspects properties. -/

#guard OpCode.getEffects (.llvm .load) (default : LoadProperties) == #[.read]
#guard OpCode.getEffects (.llvm .load) volatileLoadProperties == #[.read, .write]

#guard OpCode.getEffects (.llvm .store) (default : StoreProperties) == #[.write]
#guard OpCode.getEffects (.llvm .store) volatileStoreProperties == #[.write, .read]

#guard OpCode.getEffects (.arith .addi) (default : ArithIntegerOverflowFlagsProperties) == #[]

/- The derived queries distinguish reads from writes. -/

#guard HasOpInfo.readsMemory (OpCode.llvm .load) (default : LoadProperties)
#guard !(HasOpInfo.writesMemory (OpCode.llvm .load) (default : LoadProperties))
#guard HasOpInfo.writesMemory (OpCode.llvm .load) volatileLoadProperties

#guard HasOpInfo.writesMemory (OpCode.llvm .store) (default : StoreProperties)
#guard !(HasOpInfo.readsMemory (OpCode.llvm .store) (default : StoreProperties))
#guard HasOpInfo.readsMemory (OpCode.llvm .store) volatileStoreProperties

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
