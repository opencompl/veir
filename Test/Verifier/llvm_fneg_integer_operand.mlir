// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (f64, f32, i32)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%d: f64, %s: f32, %i: i32):
    %r = "llvm.fneg"(%i) <{fastmathFlags = #llvm.fastmath<none>}> : (i32) -> i32
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.fneg: Expected operand 0 to have floating point type
