// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `or x, (and x, y)` is `x` (absorption law): the `and x, y` is subsumed by x.
// Here the `and` is the RIGHT operand of the `or`.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64) -> i64}> ({
  ^bb0(%x: i64, %y: i64):
    %and = "llvm.and"(%x, %y) : (i64, i64) -> i64
    %r = "llvm.or"(%x, %and) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: neither `and` operand is the other `or` operand, so no absorption.
  "func.func"() <{function_type = (i64, i64, i64) -> i64}> ({
  ^bb0(%x: i64, %y: i64, %z: i64):
    %and = "llvm.and"(%x, %y) : (i64, i64) -> i64
    %r = "llvm.or"(%z, %and) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// The or/and collapse to x, which is returned directly.
// CHECK:      ^{{.*}}(%[[X:.*]] : i64, %[[Y:.*]] : i64):
// CHECK-NOT:  "llvm.or"
// CHECK:      "func.return"(%[[X]]) : (i64) -> ()

// No shared operand: the or/and survive.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i64, %[[NY:.*]] : i64, %[[NZ:.*]] : i64):
// CHECK:      %[[NAND:.*]] = "llvm.and"(%[[NX]], %[[NY]]) : (i64, i64) -> i64
// CHECK:      %[[NR:.*]] = "llvm.or"(%[[NZ]], %[[NAND]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[NR]]) : (i64) -> ()
