// RUN: veir-interpret --benchmark=2 %s | filecheck %s
// CHECK: Program output: #[0x00000008#32]
// CHECK: Execution only; 7 batches x 2 runs, 10 warmups per backend
// CHECK: Median normal:
// CHECK: Median CTree:
// CHECK: CTree / normal:
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i32}> ({
    %a = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %b = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %result = "llvm.add"(%a, %b) : (i32, i32) -> i32
    "func.return"(%result) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
