// RUN: veir-interpret %s | filecheck %s
// RUN: LLUBI
// RUN: ALIVE_EXEC

// Signed remainder by a poison divisor is immediate UB.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i32 ()>}> ({
    %lhs  = "llvm.mlir.constant"() <{ "value" = 7 : i32 }> : () -> i32
    %neg1 = "llvm.mlir.constant"() <{ "value" = -1 : i32 }> : () -> i32
    %one  = "llvm.mlir.constant"() <{ "value" = 1 : i32 }> : () -> i32
    %poison = "llvm.add"(%neg1, %one) <{"overflowFlags" = 2 : i32}> : (i32, i32) -> i32
    %y = "llvm.srem"(%lhs, %poison) : (i32, i32) -> i32
    "llvm.return"(%y) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
