// RUN: veir-interpret %s | filecheck %s

// LLUBI: reports a poison return from main as an error, so it cannot
// cross-check this test.

// Regression check: a poison dividend with a concrete safe (nonzero) divisor
// propagates as poison — NOT immediate UB.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i32 ()>}> ({
    %five = "llvm.mlir.constant"() <{ "value" = 5 : i32 }> : () -> i32
    %neg1 = "llvm.mlir.constant"() <{ "value" = -1 : i32 }> : () -> i32
    %one  = "llvm.mlir.constant"() <{ "value" = 1 : i32 }> : () -> i32
    %poison = "llvm.add"(%neg1, %one) <{"overflowFlags" = 2 : i32}> : (i32, i32) -> i32
    %y = "llvm.udiv"(%poison, %five) : (i32, i32) -> i32
    "llvm.return"(%y) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[poison]
