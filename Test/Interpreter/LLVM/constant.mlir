// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %pos = "llvm.mlir.constant"() <{ "value" = 3 : i32 }> : () -> i32
    %zero = "llvm.mlir.constant"() <{ "value" = 0 : i32 }> : () -> i32
    %neg = "llvm.mlir.constant"() <{ "value" = -4 : i32 }> : () -> i32
    %fzero = "llvm.mlir.constant"() <{ "value" = 1.0 : f64 }> : () -> f64
    "func.return"(%pos, %zero, %neg, %fzero) : (i32, i32, i32, f64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000003#32, 0x00000000#32, 0xfffffffc#32, 1.000000]
