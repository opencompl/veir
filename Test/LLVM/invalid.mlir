// RUN: veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  ^bb0(%a: i32, %b : i16):
      %sexta = "llvm.sext"(%a) : (i32) -> i16
      // CHECK: Error verifying input program: Operand's width must be smaller than result's width
}) : () -> ()

