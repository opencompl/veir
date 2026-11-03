// RUN: veir-opt %s -p=instcombine | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
    ^bb0():
      // --- Identity and annihilation patterns ---
      %zero = "llvm.mlir.constant"() <{ "value" = 0 : i32 }> : () -> i32
      %x = "test.test"() : () -> i32
      // CHECK:      %{{.*}} = "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32
      // CHECK-NEXT: %[[X:.*]] = "test.test"() : () -> i32

      // sub x - x => 0
      %sub_self = "llvm.sub"(%x, %x) : (i32, i32) -> i32
      "test.test"(%sub_self) : (i32) -> ()
      // CHECK-NEXT: %[[SUB_ZERO:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32
      // CHECK-NEXT: "test.test"(%[[SUB_ZERO]]) : (i32) -> ()
      "test.test"(%zero) : (i32) -> ()
      "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
