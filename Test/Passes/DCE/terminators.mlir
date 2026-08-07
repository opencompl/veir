// RUN: veir-opt %s -p=dce | filecheck %s

// A terminator produces no results, so nothing can use it and the unused-result
// test alone would delete it. It survives because it terminates its block, not
// because it touches memory: `cf.br` is `Pure` upstream.

"builtin.module"() ({
  "func.func"() <{function_type = (i64) -> (), sym_name = "main"}> ({
  ^bb0(%arg: i64):
    %dead = "llvm.add"(%arg, %arg) : (i64, i64) -> i64
    "cf.br"()[^bb1] : () -> ()
  ^bb1():
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// The dead add goes; both terminators stay.
// CHECK-LABEL: "func.func"() <{"function_type" = (i64) -> (), "sym_name" = "main"}>
// CHECK-NOT: "llvm.add"
// CHECK: "cf.br"() [^{{.*}}] : () -> ()
// CHECK: "func.return"() : () -> ()
