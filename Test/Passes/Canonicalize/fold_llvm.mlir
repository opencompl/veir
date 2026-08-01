// RUN: veir-opt %s -p=canonicalize,dce | filecheck %s

// Folded llvm operations materialize their constants in the llvm dialect.
"builtin.module"() ({
  "func.func"() <{function_type = () -> i64, sym_name = "fold_add"}> ({
      %c7 = "llvm.mlir.constant"() <{ "value" = 7 : i64 }> : () -> i64
      %c8 = "llvm.mlir.constant"() <{ "value" = 8 : i64 }> : () -> i64
      %sum = "llvm.add"(%c7, %c8) : (i64, i64) -> i64
      // CHECK:      %[[C15:.*]] = "llvm.mlir.constant"() <{"value" = 15 : i64}> : () -> i64
      // CHECK-NEXT: "func.return"(%[[C15]]) : (i64) -> ()
      "func.return"(%sum) : (i64) -> ()
  }) : () -> ()

  // llvm.and(x, 0) -> 0
  "func.func"() <{function_type = (i64) -> i64, sym_name = "and_zero"}> ({
    ^bb0(%x : i64):
      // CHECK:      %[[C0:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i64}> : () -> i64
      // CHECK-NEXT: "func.return"(%[[C0]]) : (i64) -> ()
      %c0 = "llvm.mlir.constant"() <{ "value" = 0 : i64 }> : () -> i64
      %r = "llvm.and"(%x, %c0) : (i64, i64) -> i64
      "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-NOT: "llvm.add"
// CHECK-NOT: "llvm.and"
