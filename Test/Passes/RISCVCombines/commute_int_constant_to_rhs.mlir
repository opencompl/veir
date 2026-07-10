// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `(C op x)` becomes `(x op C)` for add/mul/and/or/xor: a constant left operand
// is commuted to the right. It fires only when exactly the left operand is the
// constant (so it does not commute forever on `C op C`).

"builtin.module"() ({
  // add
  "func.func"() <{function_type = (i32) -> i32}> ({
  ^bb0(%x: i32):
    %c = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %r = "llvm.add"(%c, %x) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // mul
  "func.func"() <{function_type = (i32) -> i32}> ({
  ^bb0(%x: i32):
    %c = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %r = "llvm.mul"(%c, %x) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // and
  "func.func"() <{function_type = (i32) -> i32}> ({
  ^bb0(%x: i32):
    %c = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %r = "llvm.and"(%c, %x) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // or
  "func.func"() <{function_type = (i32) -> i32}> ({
  ^bb0(%x: i32):
    %c = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %r = "llvm.or"(%c, %x) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // xor
  "func.func"() <{function_type = (i32) -> i32}> ({
  ^bb0(%x: i32):
    %c = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %r = "llvm.xor"(%c, %x) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // Negative case: constant already on the right, so nothing to commute.
  "func.func"() <{function_type = (i32) -> i32}> ({
  ^bb0(%x: i32):
    %c = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %r = "llvm.add"(%x, %c) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// add: constant moves right.
// CHECK:      ^{{.*}}(%[[X0:.*]] : i32):
// CHECK:      %[[C0:.*]] = "llvm.mlir.constant"() <{"value" = 5 : i32}> : () -> i32
// CHECK:      %[[R0:.*]] = "llvm.add"(%[[X0]], %[[C0]]) : (i32, i32) -> i32
// CHECK:      "func.return"(%[[R0]]) : (i32) -> ()

// mul
// CHECK:      ^{{.*}}(%[[X1:.*]] : i32):
// CHECK:      %[[C1:.*]] = "llvm.mlir.constant"() <{"value" = 5 : i32}> : () -> i32
// CHECK:      %[[R1:.*]] = "llvm.mul"(%[[X1]], %[[C1]]) : (i32, i32) -> i32
// CHECK:      "func.return"(%[[R1]]) : (i32) -> ()

// and
// CHECK:      ^{{.*}}(%[[X2:.*]] : i32):
// CHECK:      %[[C2:.*]] = "llvm.mlir.constant"() <{"value" = 5 : i32}> : () -> i32
// CHECK:      %[[R2:.*]] = "llvm.and"(%[[X2]], %[[C2]]) : (i32, i32) -> i32
// CHECK:      "func.return"(%[[R2]]) : (i32) -> ()

// or
// CHECK:      ^{{.*}}(%[[X3:.*]] : i32):
// CHECK:      %[[C3:.*]] = "llvm.mlir.constant"() <{"value" = 5 : i32}> : () -> i32
// CHECK:      %[[R3:.*]] = "llvm.or"(%[[X3]], %[[C3]]) : (i32, i32) -> i32
// CHECK:      "func.return"(%[[R3]]) : (i32) -> ()

// xor
// CHECK:      ^{{.*}}(%[[X4:.*]] : i32):
// CHECK:      %[[C4:.*]] = "llvm.mlir.constant"() <{"value" = 5 : i32}> : () -> i32
// CHECK:      %[[R4:.*]] = "llvm.xor"(%[[X4]], %[[C4]]) : (i32, i32) -> i32
// CHECK:      "func.return"(%[[R4]]) : (i32) -> ()

// Constant already on the right: unchanged (single add, no re-commute).
// CHECK:      ^{{.*}}(%[[X5:.*]] : i32):
// CHECK:      %[[C5:.*]] = "llvm.mlir.constant"() <{"value" = 5 : i32}> : () -> i32
// CHECK:      %[[R5:.*]] = "llvm.add"(%[[X5]], %[[C5]]) : (i32, i32) -> i32
// CHECK:      "func.return"(%[[R5]]) : (i32) -> ()
