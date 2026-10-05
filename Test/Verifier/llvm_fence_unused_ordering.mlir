// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// 3 is not an ordering at all: MLIR leaves that number unused, so it is
// refused before the question of which orderings a fence accepts arises.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void ()>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
    "llvm.fence"() <{ordering = 3 : i64}> : () -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.fence: invalid ordering 3
