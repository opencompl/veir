// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (i64)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%x: i64):
    "llvm.intr.vastart"(%x) : (i64) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.intr.vastart: Expected operand 0 to have !llvm.ptr type
