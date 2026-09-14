// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// The operand must be a vector.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (i8)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%v: i8):
    %r = "llvm.intr.vector.reduce.or"(%v) : (i8) -> i8
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Expected operand 0 to have vector type
