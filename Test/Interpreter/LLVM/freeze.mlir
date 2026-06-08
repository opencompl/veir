// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i32, i32)}> ({
    %cneg = "llvm.mlir.constant"() <{ "value" = -1 : i8 }> : () -> i8
    %a = "llvm.zext"(%cneg) <{nneg}> : (i8) -> i32
    %a_freeze = "llvm.freeze"(%a) : (i32) -> i32
    "func.return"(%a, %a_freeze) : (i32, i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[poison, 0x00000000#32]
