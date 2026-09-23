module

import all Veir.Dialects.LLVM.OpInfo
import all Veir.IR.Attribute
import all Veir.Interpreter.Basic

open Veir

-- Boolean constants zero-extend even when their encoded high bit is set.
example (memory : MemoryState) :
    Llvm.interpretOp' .mlir__constant
      { value := .integer ⟨1, IntegerType.signless 1⟩ }
      #[TypeAttr.of IntegerType (IntegerType.signless 64)] #[] #[] memory .riscv64 =
      .ok (#[.int 64 (.val 1)], memory, none) := by rfl

-- An i8 attribute encoding 255 means -1 when widened to an i64 result.
example (memory : MemoryState) :
    Llvm.interpretOp' .mlir__constant
      { value := .integer ⟨255, IntegerType.signless 8⟩ }
      #[TypeAttr.of IntegerType (IntegerType.signless 64)] #[] #[] memory .riscv64 =
      .ok (#[.int 64 (.val (-1))], memory, none) := by rfl
