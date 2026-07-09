// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `(A - B) - 1` equals `A + ~B` (since `-B - 1 == ~B`), so it rewrites to
// `add (xor B, -1), A`.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64) -> i64}> ({
  ^bb0(%a: i64, %b: i64):
    %sub = "llvm.sub"(%a, %b) : (i64, i64) -> i64
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %r = "llvm.sub"(%sub, %one) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: subtracting 2 (not 1) from the inner sub does not match.
  "func.func"() <{function_type = (i64, i64) -> i64}> ({
  ^bb0(%a: i64, %b: i64):
    %sub = "llvm.sub"(%a, %b) : (i64, i64) -> i64
    %two = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %r = "llvm.sub"(%sub, %two) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// Rewritten to add(xor(B, -1), A).
// CHECK:      ^{{.*}}(%[[A:.*]] : i64, %[[B:.*]] : i64):
// CHECK:      %[[M1:.*]] = "llvm.mlir.constant"() <{"value" = -1 : i64}> : () -> i64
// CHECK:      %[[NB:.*]] = "llvm.xor"(%[[B]], %[[M1]]) : (i64, i64) -> i64
// CHECK:      %[[R:.*]] = "llvm.add"(%[[NB]], %[[A]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[R]]) : (i64) -> ()

// Subtracting 2: the pattern does not fire.
// CHECK:      ^{{.*}}(%[[NA:.*]] : i64, %[[NB2:.*]] : i64):
// CHECK:      %[[NSUB:.*]] = "llvm.sub"(%[[NA]], %[[NB2]]) : (i64, i64) -> i64
// CHECK:      %[[NR:.*]] = "llvm.sub"(%[[NSUB]],
// CHECK:      "func.return"(%[[NR]]) : (i64) -> ()
