// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i32, i32)}> ({
    %a = "llvm.mlir.poison"() : () -> i32
    %a_freeze = "llvm.freeze"(%a) : (i32) -> i32
    "func.return"(%a, %a_freeze) : (i32, i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[poison, 0x00000000#32]
