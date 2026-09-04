// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i32, i8)}> ({
    %zero_i32 = "llvm.mlir.zero"() : () -> i32
    %zero_i8 = "llvm.mlir.zero"() : () -> i8
    "func.return"(%zero_i32, %zero_i8) : (i32, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000000#32, 0x00#8]
