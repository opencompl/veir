// RUN: veir-opt %s -p=instcombine | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
    ^bb0():
      // --- DeMorgan patterns ---
      %m1 = "llvm.mlir.constant"() <{ "value" = -1 : i32 }> : () -> i32
      %a = "test.test"() : () -> i32
      %b = "test.test"() : () -> i32
      // CHECK:      %[[A:.*]] = "test.test"() : () -> i32
      // CHECK-NEXT: %[[B:.*]] = "test.test"() : () -> i32

      // ~(~a | ~b) => a & b
      %na2 = "llvm.xor"(%a, %m1) : (i32, i32) -> i32
      %nb2 = "llvm.xor"(%b, %m1) : (i32, i32) -> i32
      %or2 = "llvm.or"(%na2, %nb2) : (i32, i32) -> i32
      %demorgan_and = "llvm.xor"(%or2, %m1) : (i32, i32) -> i32
      "test.test"(%demorgan_and) : (i32) -> ()
      // CHECK-NEXT: %[[AND:.*]] = "llvm.and"(%[[A]], %[[B]]) : (i32, i32) -> i32
      // CHECK-NEXT: "test.test"(%[[AND]]) : (i32) -> ()
      "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
