module

import Veir.Pass
meta import Veir.GlobalOpInfo

open Veir

/-! Dialects registered in the global opcode type have a generated membership instance. -/

example : HasDialect OpCode Arith := inferInstance
example : HasDialect OpCode Builtin := inferInstance

/-! Dialect-local and global operation name lookup is generated. -/
#guard Arith.fromName "arith.addi".toUTF8 = some .addi
#guard Arith.fromName "llvm.add".toUTF8 = none
#guard Arith.name .addi = "arith.addi".toUTF8
#guard OpCode.fromName "arith.addi".toUTF8 = some (.arith .addi)
#guard OpCode.fromName "unknown.op".toUTF8 = none
#guard OpCode.name (.arith .addi) = "arith.addi".toUTF8
#guard HasDialectOpInfo.fromName (opCode := Arith) "arith.addi".toUTF8 = some .addi
#guard HasDialectOpInfo.name (opCode := Arith) .addi = "arith.addi".toUTF8

/-! Dialects can define conversion functions to and from the global opcode type. -/
abbrev Veir.Arith.from? (op : OpInfo) [HasOpInfo OpInfo] [HasDialect OpInfo Arith]
    : Option Arith :=
  toDialect? Arith op

/-! Some tests for the conversion functions from and to the global opcode type. -/
#guard Arith.from? (Arith.addi : OpCode) = some Arith.addi
#guard Arith.from? (OpCode.builtin .module) = none

/--
A minimal pass that can be instantiated for any ambient opcode type containing
the Arith dialect. It exercises both opcode projection and property transport.
-/
private def genericArithAwarePass {OpInfo : Type} [HasOpInfo OpInfo]
    [HasDialect OpInfo Arith] : Pass OpInfo where
  name := "generic-arith-aware-test"
  description := "Compile-time test for dialect-generic passes."
  run := fun _ ctx op _ => do
    /- Matching an `arith` operation, here an `addi`. -/
    let some .addi := Arith.from? (op.getOpType! ctx.raw) | return ctx
    /- Getting the property of an operation with a type based on the dialect. -/
    let _a : ArithIntegerOverflowFlagsProperties := op.getProperties! ctx.raw Arith.addi
    /- Set dialect-local properties. -/
    let props := ArithIntegerOverflowFlagsProperties.mk { nsw := true, nuw := false }
    let ctx := WfRewriter.setProperties! (Dialect := Arith) ctx op Arith.addi props
    return ctx

example : Pass OpCode := genericArithAwarePass
