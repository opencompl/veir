// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  ^1():
    %x1 = "llvm.mlir.constant"() <{"value" = 8 : i32}> : () -> i32
    %x2 = "llvm.mlir.constant"() <{"value" = 11 : i32}> : () -> i32
    "llvm.br"(%x1, %x2) [^2] : (i32, i32) -> ()
  ^2(%y1 : i32, %y2 : i32):
    "llvm.return"(%y2) : (i32) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000b#32]
