// RUN: not veir-opt %s 2>&1 | filecheck %s
//
// Zero-width integers (`i0`) are forbidden by construction: `IntegerType`
// carries a positivity invariant, so the parser cannot build an i0-typed
// value. An `llvm.func` operating on i0 is therefore rejected at parse time,
// before any pass or verifier runs.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "f", function_type = !llvm.func<i0 (i0, i0)>}> ({
  ^bb0(%arg0: i0, %arg1: i0):
    %0 = "llvm.add"(%arg0, %arg1) : (i0, i0) -> i0
    %1 = "llvm.mul"(%0, %arg0) : (i0, i0) -> i0
    "llvm.return"(%1) : (i0) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: zero-width integer type 'i0' is not supported
