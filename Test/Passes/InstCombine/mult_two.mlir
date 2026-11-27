// RUN: veir-opt %s -p=instcombine | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
    ^bb0():
      %two = "llvm.mlir.constant"() <{ "value" = 2 : i32 }> : () -> i32
      %a = "test.test"() : () -> i32
      // CHECK: %{{.*}} = "test.test"() : () -> i32

      %mul_two = "llvm.mul"(%a, %two) <{overflowFlags = 3 : i32}> : (i32, i32) -> i32
      "test.test"(%mul_two) : (i32) -> ()
      // CHECK-NEXT: %{{.*}} = "llvm.add"(%{{.*}}, %{{.*}}) <{"overflowFlags" = 3 : i32}> : (i32, i32) -> i32
      // CHECK-NEXT: "test.test"(%{{.*}}) : (i32) -> ()

      %neg_two = "llvm.mlir.constant"() <{ "value" = 2 : i2 }> : () -> i2
      %x = "test.test"() : () -> i2
      %mul_neg_two = "llvm.mul"(%x, %neg_two) <{overflowFlags = 1 : i32}> : (i2, i2) -> i2
      "test.test"(%mul_neg_two) : (i2) -> ()
      // CHECK: "llvm.mul"(%{{.*}}, %{{.*}}) <{"overflowFlags" = 1 : i32}> : (i2, i2) -> i2
      "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
