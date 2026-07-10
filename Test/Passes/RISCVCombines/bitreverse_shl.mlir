// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `bitreverse(shl(bitreverse x), y)` is `lshr x, y`: reverse, shift left, reverse
// again equals a single logical right shift.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64) -> i64}> ({
  ^bb0(%x: i64, %y: i64):
    %bx = "llvm.intr.bitreverse"(%x) : (i64) -> i64
    %s = "llvm.shl"(%bx, %y) : (i64, i64) -> i64
    %r = "llvm.intr.bitreverse"(%s) : (i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: the inner value is not a bitreverse, so the pattern does not fire.
  "func.func"() <{function_type = (i64, i64) -> i64}> ({
  ^bb0(%x: i64, %y: i64):
    %s = "llvm.shl"(%x, %y) : (i64, i64) -> i64
    %r = "llvm.intr.bitreverse"(%s) : (i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// The reverse/shl/reverse sandwich collapses to a single lshr.
// CHECK:      ^{{.*}}(%[[X:.*]] : i64, %[[Y:.*]] : i64):
// CHECK:      %[[R:.*]] = "llvm.lshr"(%[[X]], %[[Y]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[R]]) : (i64) -> ()

// Non-bitreverse inner operand: the outer bitreverse survives.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i64, %[[NY:.*]] : i64):
// CHECK:      %[[NS:.*]] = "llvm.shl"(%[[NX]], %[[NY]]) : (i64, i64) -> i64
// CHECK:      %[[NR:.*]] = "llvm.intr.bitreverse"(%[[NS]]) : (i64) -> i64
// CHECK:      "func.return"(%[[NR]]) : (i64) -> ()
