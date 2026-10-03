// RUN: veir-interpret %s | filecheck %s
// RUN: LLUBI
// RUN: ALIVE_EXEC

// Unsigned remainder with a concrete zero divisor is immediate UB.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i32 ()>}> ({
    %lhs = "llvm.mlir.constant"() <{ "value" = 130 : i32 }> : () -> i32
    %zero = "llvm.mlir.constant"() <{ "value" = 0 : i32 }> : () -> i32
    %y = "llvm.urem"(%lhs, %zero) : (i32, i32) -> i32
    "llvm.return"(%y) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
