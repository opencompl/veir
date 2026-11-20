// XFAIL: ctree
// RUN: CTREE

// A negative test of the CTree interpretation itself: the function returns 7
// and the CHECK line below asks for 8, so the CTree run must fail rather than
// pass vacuously. Were the CTREE substitution broken, this test would pass
// and lit would report the unexpected pass.

// NO_CROSS_CHECK: a negative test of the CTREE substitution, not of the semantics of a program

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %v = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    "llvm.return"(%v) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000008#64]
