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

#guard OpCode.getEffects (.llvm .alloca) (default : AllocaProperties) == .allocate

#guard OpCode.getEffects (.arith .addi) (default : ArithIntegerOverflowFlagsProperties) == .none

/- RISC-V models volatility the same way, on its own load and store opcodes. -/

#guard OpCode.getEffects (.riscv .lw) (default : RISCVMemProperties) == .read
#guard OpCode.getEffects (.riscv .lw) volatileMemProperties == .readWrite

#guard OpCode.getEffects (.riscv .sw) (default : RISCVMemProperties) == .write
#guard OpCode.getEffects (.riscv .sw) volatileMemProperties == .readWrite

#guard OpCode.getEffects (.riscv .add) (default : Unit) == .none

#guard OpCode.getEffects (.riscv_stack .alloca)
  (default : RISCVStackAllocaProperties) == .allocate

/-
  A call is conservative in both directions: we have no interprocedural effect
  analysis, so the callee may do anything. Upstream reaches the same answer by
  a different route, as `func.call` implements no memory effect interface at
  all and so has unknown effects.
-/

#guard OpCode.getEffects (.func .call) (default : FuncCallProperties) == .unknown

/- Operations carrying regions conservatively have every modeled memory effect. -/

/-- A `builtin.module` op, which always carries a single region. -/
private def moduleWithRegion : OperationPtr × IRContext OpCode :=
  let (ctx, moduleOp) := WfIRContext.create! OpCode
  (moduleOp, ctx.raw)

#guard moduleWithRegion.1.getEffects moduleWithRegion.2 == .unknown
#guard !moduleWithRegion.1.isMemoryIndependent moduleWithRegion.2

/- Executable memory independence is derived from the complete memory-effect summary. -/

private def opWithType {Dialect : Type} [HasOpInfo Dialect] [HasDialect OpCode Dialect]
    (opType : Dialect) (properties : propertiesOf opType) :
    OperationPtr × IRContext OpCode :=
  let (ctx, moduleOp) := WfIRContext.create! OpCode
  let moduleRegion := moduleOp.getRegion! ctx.raw 0
  let moduleBlock := (moduleRegion.get! ctx.raw).firstBlock.get!
  let (ctx, op) :=
    (WfRewriter.createOp! ctx opType #[] #[] #[] #[] properties
      (some (.atEnd moduleBlock))).get!
  (op, ctx.raw)

#guard let (op, ctx) := opWithType Arith.addi default; op.isMemoryIndependent ctx
#guard let (op, ctx) := opWithType Llvm.load default; !op.isMemoryIndependent ctx
#guard let (op, ctx) := opWithType Llvm.store default; !op.isMemoryIndependent ctx
#guard let (op, ctx) := opWithType Llvm.alloca default; !op.isMemoryIndependent ctx
