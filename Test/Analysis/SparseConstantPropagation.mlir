// RUN: veir-opt %s -p=print-sccp | filecheck %s

"builtin.module"() ({
  // CHECK:      // dataflow.liveness block entry = live
  "func.func"() <{function_type = (i32) -> (), sym_name = "poison"}> ({
  ^entry(%unknown : i32):
    // CHECK-NEXT: // dataflow.liveness block entry = live
    // CHECK-NEXT: // dataflow.constant block argument 0 = top
    %poison = "llvm.mlir.poison"() : () -> i32
    // CHECK-NEXT: // dataflow.constant llvm.mlir.poison result 0 = const(poison : i32)
    %result = "arith.addi"(%unknown, %poison) : (i32, i32) -> i32
    // CHECK-NEXT: // dataflow.constant arith.addi result 0 = const(poison : i32)
    "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{function_type = () -> (), sym_name = "liveness"}> ({
  ^entry:
    // CHECK-NEXT: // dataflow.liveness block entry = live
    %source = "arith.constant"() <{value = 2 : i32}> : () -> i32
    // CHECK-NEXT: // dataflow.constant arith.constant result 0 = const(0x00000002#32 : i32)
    "cf.br"(%source) [^live] : (i32) -> ()
    // CHECK-NEXT: // dataflow.liveness cf.br successor 0 = live
  ^dead:
    // CHECK-NEXT: // dataflow.liveness block entry = dead
    %dead_value = "arith.constant"() <{value = 1 : i32}> : () -> i32
    // CHECK-NEXT: // dataflow.constant arith.constant result 0 = bottom
    "func.return"() : () -> ()
  ^live(%forwarded : i32):
    // CHECK-NEXT: // dataflow.liveness block entry = live
    // CHECK-NEXT: // dataflow.constant block argument 0 = const(0x00000002#32 : i32)
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
