// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<i1 (f64, f64)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%a: f64, %b: f64):
    %r = "llvm.fcmp"(%a, %b) <{fastmathFlags = #llvm.fastmath<none>, predicate = 2 : i32}> : (f64, f64) -> i1
    "llvm.return"(%r) : (i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.fcmp: expected predicate to be an i64 integer attribute, but got 2 : i32
