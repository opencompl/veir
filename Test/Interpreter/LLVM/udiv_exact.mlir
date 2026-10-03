// RUN: veir-interpret %s | filecheck %s
// RUN: LLUBI


"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i32 ()>}> ({
    %lhs = "llvm.mlir.constant"() <{ "value" = 7 : i32 }> : () -> i32
    %rhs = "llvm.mlir.constant"() <{ "value" = 2 : i32 }> : () -> i32
    %x = "llvm.udiv"(%lhs, %rhs) <{isExact}> : (i32, i32) -> i32
    "llvm.return"(%x) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[poison]
