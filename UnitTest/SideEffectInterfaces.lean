import Veir.GlobalOpInfo
import Veir.Interfaces.SideEffectInterfaces
import Veir.Rewriter.WfRewriter.Basic

open Veir

private def volatileLoadProperties : LoadProperties :=
  { (default : LoadProperties) with volatile_ := true }

private def volatileStoreProperties : StoreProperties :=
  { (default : StoreProperties) with volatile_ := true }

/- The memory-effect queries distinguish reads from writes and inspect properties. -/

#guard OpCode.readsMemory (.llvm .load) (default : LoadProperties)
#guard !(OpCode.writesMemory (.llvm .load) (default : LoadProperties))
#guard OpCode.writesMemory (.llvm .load) volatileLoadProperties

#guard OpCode.writesMemory (.llvm .store) (default : StoreProperties)
#guard !(OpCode.readsMemory (.llvm .store) (default : StoreProperties))
#guard OpCode.readsMemory (.llvm .store) volatileStoreProperties

/- Operations carrying regions are conservatively treated as reading and writing. -/

/-- A `builtin.module` op, which always carries a single region. -/
private def moduleWithRegion : OperationPtr × IRContext OpCode :=
  let (ctx, moduleOp) := WfIRContext.create! OpCode
  (moduleOp, ctx.raw)

#guard moduleWithRegion.1.readsMemory moduleWithRegion.2
#guard moduleWithRegion.1.writesMemory moduleWithRegion.2
