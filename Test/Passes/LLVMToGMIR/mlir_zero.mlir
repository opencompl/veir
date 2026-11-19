// RUN: veir-opt %s -p=llvm-to-gmir | filecheck %s

// `llvm.mlir.zero` of an integer up to `i64` or a pointer becomes `g_constant 0`.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "zeros", function_type = !llvm.func<void ()>}> ({
  ^bb0():
    // CHECK:      "gmir.g_constant"() <{"value" = 0 : i64}> : () -> i64
    // CHECK-NEXT: "llvm.mlir.zero"() : () -> i128
    // CHECK-NEXT: "gmir.g_constant"() <{"value" = 0 : i64}> : () -> !llvm.ptr
    %i64 = "llvm.mlir.zero"() : () -> i64
    %i128 = "llvm.mlir.zero"() : () -> i128
    %ptr = "llvm.mlir.zero"() : () -> !llvm.ptr
    "test.test"(%i64, %i128, %ptr) : (i64, i128, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
