// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %cpos = "llvm.constant"() <{ "value" = 42 : i8 }> : () -> i8
  %cneg = "llvm.constant"() <{ "value" = -1 : i8 }> : () -> i8
  %a = "llvm.zext"(%cpos) <{nneg}> : (i8) -> i32
  %b = "llvm.zext"(%cneg) <{nneg}> : (i8) -> i32
  "func.return"(%a, %b) : (i32, i32) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000002a#32, poison]
