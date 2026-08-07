// RUN: veir-opt %s -p=dce | filecheck %s

// `llvm.freeze` and `llvm.bitcast` are `Pure` upstream, so an unused one is
// dead. Both were previously pinned in place by a conservative side-effect
// answer that the memory-effect queries do not repeat.

"builtin.module"() ({
  "func.func"() <{function_type = (i64) -> (), sym_name = "main"}> ({
  ^bb0(%arg: i64):
    %frozen = "llvm.freeze"(%arg) : (i64) -> i64
    %cast = "llvm.bitcast"(%arg) : (i64) -> i64
    "test.test"(%arg) : (i64) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: "func.func"() <{"function_type" = (i64) -> (), "sym_name" = "main"}>
// CHECK-NOT: "llvm.freeze"
// CHECK-NOT: "llvm.bitcast"
// CHECK: "test.test"(%{{.*}}) : (i64) -> ()
// CHECK-NEXT: "func.return"() : () -> ()
