// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (f64, f32)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%d: f64, %s: f32):
    %r = "llvm.fadd"(%d, %s) : (f64, f32) -> f64
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.fadd: Expected operands to have the same type
