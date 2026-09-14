// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (f64)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%d: f64):
    %r = "llvm.fmul"(%d, %d) : (f64, f64) -> i32
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.fmul: Expected result type to match operand type
