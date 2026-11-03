// REQUIRES: llubi
// XFAIL: *
// RUN: LLUBI
// RUN: ALIVE_EXEC

// A negative test of the cross-check itself: the function returns 7 and the
// CHECK line below asks for 8, so the llubi run must fail rather than pass
// vacuously. Were the LLUBI substitution broken, this test would pass and
// lit would report the unexpected pass.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %v = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    "llvm.return"(%v) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000008#64]
