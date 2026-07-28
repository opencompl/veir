// RUN: veir-opt %s -p=instcombine | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
    ^bb0():
      %two = "llvm.mlir.constant"() <{ "value" = 2 : i32 }> : () -> i32
      %a = "test.test"() : () -> i32
      // CHECK: %{{.*}} = "test.test"() : () -> i32

      %mul_two = "llvm.mul"(%a, %two) : (i32, i32) -> i32
      "test.test"(%mul_two) : (i32) -> ()
      // CHECK-NEXT: %{{.*}} = "llvm.add"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
      // CHECK-NEXT: "test.test"(%{{.*}}) : (i32) -> ()
      "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
