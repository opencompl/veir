// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// Negating an `icmp sge` flips the predicate: `not (icmp sge X Y)` becomes
// `icmp slt X Y`.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64) -> i1}> ({
  ^bb0(%x: i64, %y: i64):
    %cmp = "llvm.icmp"(%x, %y) <{predicate = 5 : i64}> : (i64, i64) -> i1
    %m1 = "llvm.mlir.constant"() <{value = -1 : i1}> : () -> i1
    %r = "llvm.xor"(%cmp, %m1) : (i1, i1) -> i1
    "func.return"(%r) : (i1) -> ()
  }) : () -> ()

  // Negative case: xor with 1 (not all-ones for a wider type) — here the value is
  // still on i1 but xored against a non-icmp, so nothing folds.
  "func.func"() <{function_type = (i64, i64, i1) -> i1}> ({
  ^bb0(%x: i64, %y: i64, %b: i1):
    %m1 = "llvm.mlir.constant"() <{value = -1 : i1}> : () -> i1
    %r = "llvm.xor"(%b, %m1) : (i1, i1) -> i1
    "func.return"(%r) : (i1) -> ()
  }) : () -> ()
}) : () -> ()

// The not folds into the comparison with the inverted predicate.
// CHECK:      ^{{.*}}(%[[X:.*]] : i64, %[[Y:.*]] : i64):
// CHECK:      %[[R:.*]] = "llvm.icmp"(%[[X]], %[[Y]]) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
// CHECK:      "func.return"(%[[R]]) : (i1) -> ()

// Not a negated icmp: the xor survives.
// CHECK:      ^{{.*}}(%{{.*}} : i64, %{{.*}} : i64, %[[B:.*]] : i1):
// CHECK:      %[[NM1:.*]] = "llvm.mlir.constant"() <{"value" = -1 : i1}> : () -> i1
// CHECK:      %[[NR:.*]] = "llvm.xor"(%[[B]], %[[NM1]]) : (i1, i1) -> i1
// CHECK:      "func.return"(%[[NR]]) : (i1) -> ()
