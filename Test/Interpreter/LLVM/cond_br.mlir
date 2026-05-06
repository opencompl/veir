// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  ^1():
    %x1 = "llvm.constant"() <{"value" = 8 : i32}> : () -> i32
    %x2 = "llvm.constant"() <{"value" = 11 : i32}> : () -> i32
    %cond = "llvm.constant"() <{"value" = 0 : i1}> : () -> i1
    "llvm.cond_br"(%cond, %x1, %x2) [^4,^3] <{"operandSegmentSizes" = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
  ^2(%y : i32):
    "llvm.return"(%y) : (i32) -> ()
  ^3(%z1 : i32):
    %z2 = "llvm.constant"() <{"value" = 2 : i32}> : () -> i32
    %cond = "llvm.constant"() <{"value" = -1 : i1}> : () -> i1
    "llvm.cond_br"(%cond, %z1, %z2) [^2,^4] <{"operandSegmentSizes" = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
  ^4(%a1 : i32):
    %a2 = "llvm.constant"() <{"value" = 5 : i32}> : () -> i32
    "llvm.return"(%a2) : (i32) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000b#32]
