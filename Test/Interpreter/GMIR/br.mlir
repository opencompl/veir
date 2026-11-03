// RUN: veir-interpret %s | filecheck %s

// `g_brcond` takes its first successor when its condition is nonzero, also for a condition wider
// than `i1`, and `g_br` forwards its operands to its successor.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i64, i64)}> ({
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %two = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %t = "llvm.mlir.constant"() <{value = 10 : i64}> : () -> i64
    %f = "llvm.mlir.constant"() <{value = 20 : i64}> : () -> i64
    "gmir.g_brcond"(%two, %t, %f) [^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i64, i64, i64) -> ()
  ^bb1(%a: i64):
    "gmir.g_brcond"(%zero, %t, %f) [^bb2, ^bb3] <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i64, i64, i64) -> ()
  ^bb2(%b: i64):
    "func.return"(%b, %b, %b) : (i64, i64, i64) -> ()
  ^bb3(%c: i64):
    "gmir.g_br"(%a, %c) [^bb4] : (i64, i64) -> ()
  ^bb4(%x: i64, %y: i64):
    "func.return"(%x, %y, %two) : (i64, i64, i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000000a#64, 0x0000000000000014#64, 0x0000000000000002#64]
