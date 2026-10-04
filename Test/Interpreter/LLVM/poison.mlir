// RUN: veir-interpret %s | filecheck %s
// RUN: LLUBI
// RUN: ALIVE_EXEC

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i32, i64)}> ({
    %one = "llvm.mlir.poison"() : () -> i32
    %two = "llvm.mlir.poison"() : () -> i64
    "func.return"(%one, %two) : (i32, i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: #[poison, poison]
