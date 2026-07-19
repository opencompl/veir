// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `icmp pred C, x` is canonicalized to `icmp swap(pred) x, C`: a constant left
// operand moves to the right and the predicate flips to its swapped form
// (slt<->sgt, ult<->ugt, sle<->sge, ule<->uge; eq/ne unchanged). Fires only when
// exactly the left operand is constant, so it does not oscillate.

"builtin.module"() ({
  // slt with constant on the left -> sgt with constant on the right.
  "func.func"() <{function_type = (i32) -> i1, sym_name = "foo"}> ({
  ^bb0(%x: i32):
    %c = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %r = "llvm.icmp"(%c, %x) <{predicate = 2 : i64}> : (i32, i32) -> i1
    "func.return"(%r) : (i1) -> ()
  }) : () -> ()

  // eq is symmetric: predicate is unchanged, operands still swapped.
  "func.func"() <{function_type = (i32) -> i1, sym_name = "bar"}> ({
  ^bb0(%x: i32):
    %c = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %r = "llvm.icmp"(%c, %x) <{predicate = 0 : i64}> : (i32, i32) -> i1
    "func.return"(%r) : (i1) -> ()
  }) : () -> ()

  // Negative case: constant already on the right, so nothing to canonicalize.
  "func.func"() <{function_type = (i32) -> i1, sym_name = "baz"}> ({
  ^bb0(%x: i32):
    %c = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %r = "llvm.icmp"(%x, %c) <{predicate = 2 : i64}> : (i32, i32) -> i1
    "func.return"(%r) : (i1) -> ()
  }) : () -> ()
}) : () -> ()

// slt C, x  ->  sgt x, C  (predicate 2 = slt, 4 = sgt in the LLVM encoding).
// CHECK:      ^{{.*}}(%[[X0:.*]] : i32):
// CHECK:      %[[C0:.*]] = "llvm.mlir.constant"() <{"value" = 5 : i32}> : () -> i32
// CHECK:      %[[R0:.*]] = "llvm.icmp"(%[[X0]], %[[C0]]) <{"predicate" = 4 : i64}> : (i32, i32) -> i1
// CHECK:      "func.return"(%[[R0]]) : (i1) -> ()

// eq C, x  ->  eq x, C  (predicate 0 unchanged).
// CHECK:      ^{{.*}}(%[[X1:.*]] : i32):
// CHECK:      %[[C1:.*]] = "llvm.mlir.constant"() <{"value" = 5 : i32}> : () -> i32
// CHECK:      %[[R1:.*]] = "llvm.icmp"(%[[X1]], %[[C1]]) <{"predicate" = 0 : i64}> : (i32, i32) -> i1
// CHECK:      "func.return"(%[[R1]]) : (i1) -> ()

// Constant already on the right: unchanged (still slt x, C — no re-canonicalize).
// CHECK:      ^{{.*}}(%[[X2:.*]] : i32):
// CHECK:      %[[C2:.*]] = "llvm.mlir.constant"() <{"value" = 5 : i32}> : () -> i32
// CHECK:      %[[R2:.*]] = "llvm.icmp"(%[[X2]], %[[C2]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK:      "func.return"(%[[R2]]) : (i1) -> ()
