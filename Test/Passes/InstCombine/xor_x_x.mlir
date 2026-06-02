// RUN: veir-opt %s -p=instcombine | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
    ^bb0():
      // --- Identity and annihilation patterns ---
      %zero = "llvm.mlir.constant"() <{ "value" = 0 : i32 }> : () -> i32
      %x = "test.test"() : () -> i32
      // CHECK:      %{{.*}} = "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32
      // CHECK-NEXT: %[[X:.*]] = "test.test"() : () -> i32

      // xor x ^ x => 0
      %xor_self = "llvm.xor"(%x, %x) : (i32, i32) -> i32
      "test.test"(%xor_self) : (i32) -> ()
      // CHECK-NEXT: %[[XOR_ZERO:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32
      // CHECK-NEXT: "test.test"(%[[XOR_ZERO]]) : (i32) -> ()
      "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
