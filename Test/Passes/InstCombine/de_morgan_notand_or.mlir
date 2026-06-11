// RUN: veir-opt %s -p=instcombine | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
    ^bb0():
      // --- DeMorgan patterns ---
      %m1 = "llvm.mlir.constant"() <{ "value" = -1 : i32 }> : () -> i32
      %a = "test.test"() : () -> i32
      %b = "test.test"() : () -> i32
      // CHECK:      %[[M1:.*]] = "llvm.mlir.constant"() <{"value" = -1 : i32}> : () -> i32
      // CHECK-NEXT: %[[A:.*]] = "test.test"() : () -> i32
      // CHECK-NEXT: %[[B:.*]] = "test.test"() : () -> i32

      // ~(~a & ~b) => a | b
      %na1 = "llvm.xor"(%a, %m1) : (i32, i32) -> i32
      %nb1 = "llvm.xor"(%b, %m1) : (i32, i32) -> i32
      %and1 = "llvm.and"(%na1, %nb1) : (i32, i32) -> i32
      %demorgan_or = "llvm.xor"(%and1, %m1) : (i32, i32) -> i32
      "test.test"(%demorgan_or) : (i32) -> ()
      // CHECK-NEXT: %{{.*}} = "llvm.xor"(%[[A]], %[[M1]]) : (i32, i32) -> i32
      // CHECK-NEXT: %{{.*}} = "llvm.xor"(%[[B]], %[[M1]]) : (i32, i32) -> i32
      // CHECK-NEXT: %{{.*}} = "llvm.and"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
      // CHECK-NEXT: %[[OR:.*]] = "llvm.or"(%[[A]], %[[B]]) : (i32, i32) -> i32
      // CHECK-NEXT: "test.test"(%[[OR]]) : (i32) -> ()
      "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
