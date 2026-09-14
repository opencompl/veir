// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<i32 (f64, f64)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%a: f64, %b: f64):
    %r = "llvm.fcmp"(%a, %b) <{fastmathFlags = #llvm.fastmath<none>, predicate = 1 : i64}> : (f64, f64) -> i32
    "llvm.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.fcmp: Expected i1 result
