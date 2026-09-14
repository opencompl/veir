// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (f64, f32, i32)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%d: f64, %s: f32, %i: i32):
    %r = "llvm.intr.fmuladd"(%d, %s, %d) <{fastmathFlags = #llvm.fastmath<none>}> : (f64, f32, f64) -> f64
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.intr.fmuladd: Expected operands to have the same type
