// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// A funnel shift amount is taken modulo the bit-width, so an over-large constant
// amount is reduced to its residue: `fshl/fshr x, y, C -> fshl/fshr x, y, C % bw`
// when `C >= bw`.

"builtin.module"() ({
  // fshl by 35 on i32 reduces the amount to 35 % 32 = 3.
  "func.func"() <{function_type = (i32, i32) -> i32}> ({
  ^bb0(%x: i32, %y: i32):
    %c = "llvm.mlir.constant"() <{value = 35 : i32}> : () -> i32
    %r = "llvm.intr.fshl"(%x, %y, %c) : (i32, i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // fshr by 40 on i32 reduces the amount to 40 % 32 = 8.
  "func.func"() <{function_type = (i32, i32) -> i32}> ({
  ^bb0(%x: i32, %y: i32):
    %c = "llvm.mlir.constant"() <{value = 40 : i32}> : () -> i32
    %r = "llvm.intr.fshr"(%x, %y, %c) : (i32, i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // Negative case: the amount is already less than the width, so it stays.
  "func.func"() <{function_type = (i32, i32) -> i32}> ({
  ^bb0(%x: i32, %y: i32):
    %c = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %r = "llvm.intr.fshl"(%x, %y, %c) : (i32, i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// fshl amount reduced to 3.
// CHECK:      ^{{.*}}(%[[X:.*]] : i32, %[[Y:.*]] : i32):
// CHECK:      %[[A:.*]] = "llvm.mlir.constant"() <{"value" = 3 : i32}> : () -> i32
// CHECK:      %[[R:.*]] = "llvm.intr.fshl"(%[[X]], %[[Y]], %[[A]]) : (i32, i32, i32) -> i32
// CHECK:      "func.return"(%[[R]]) : (i32) -> ()

// fshr amount reduced to 8.
// CHECK:      ^{{.*}}(%[[X2:.*]] : i32, %[[Y2:.*]] : i32):
// CHECK:      %[[A2:.*]] = "llvm.mlir.constant"() <{"value" = 8 : i32}> : () -> i32
// CHECK:      %[[R2:.*]] = "llvm.intr.fshr"(%[[X2]], %[[Y2]], %[[A2]]) : (i32, i32, i32) -> i32
// CHECK:      "func.return"(%[[R2]]) : (i32) -> ()

// In-range amount: the funnel shift is unchanged.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i32, %[[NY:.*]] : i32):
// CHECK:      %[[NC:.*]] = "llvm.mlir.constant"() <{"value" = 5 : i32}> : () -> i32
// CHECK:      %[[NR:.*]] = "llvm.intr.fshl"(%[[NX]], %[[NY]], %[[NC]]) : (i32, i32, i32) -> i32
// CHECK:      "func.return"(%[[NR]]) : (i32) -> ()
