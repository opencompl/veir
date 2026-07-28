// RUN: veir-opt %s -p=instcombine | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
    ^bb0():
      // --- DeMorgan patterns ---
      %m1 = "llvm.mlir.constant"() <{ "value" = -1 : i32 }> : () -> i32
      %a = "test.test"() : () -> i32
      // CHECK:      %[[A:.*]] = "test.test"() : () -> i32

      // ~~a => a
      %na0 = "llvm.xor"(%a, %m1) : (i32, i32) -> i32
      %nna = "llvm.xor"(%na0, %m1) : (i32, i32) -> i32
      "test.test"(%nna) : (i32) -> ()
      // CHECK-NEXT: "test.test"(%[[A]]) : (i32) -> ()
      "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
