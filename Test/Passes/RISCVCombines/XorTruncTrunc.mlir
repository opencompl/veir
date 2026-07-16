// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// A truncation distributes over `xor`: truncating the inputs then xoring keeps exactly the low bits that xoring-then-truncating would. The two casts are hoisted through
// the bitwise op: `(trunc X) xor (trunc Y) -> trunc (X xor Y)`, doing the
// bitwise op on the narrow operands and casting once.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64) -> i32, sym_name = "foo"}> ({
  ^bb0(%x: i64, %y: i64):
    %ex = "llvm.trunc"(%x) : (i64) -> i32
    %ey = "llvm.trunc"(%y) : (i64) -> i32
    %r = "llvm.xor"(%ex, %ey) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // Negative case: only one operand is a `trunc`, so nothing is hoisted.
  "func.func"() <{function_type = (i64, i32) -> i32, sym_name = "bar"}> ({
  ^bb0(%x: i64, %y: i32):
    %ex = "llvm.trunc"(%x) : (i64) -> i32
    %r = "llvm.xor"(%ex, %y) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// The bitwise op runs on the narrow operands, then a single `trunc` widens.
// CHECK:      ^{{.*}}(%[[X:.*]] : i64, %[[Y:.*]] : i64):
// CHECK:      %[[OP:.*]] = "llvm.xor"(%[[X]], %[[Y]]) : (i64, i64) -> i64
// CHECK-NEXT: %[[E:.*]] = "llvm.trunc"(%[[OP]]) : (i64) -> i32
// CHECK:      "func.return"(%[[E]]) : (i32) -> ()

// Single cast: the pattern does not fire.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i64, %[[NY:.*]] : i32):
// CHECK:      %[[NEX:.*]] = "llvm.trunc"(%[[NX]]) : (i64) -> i32
// CHECK:      %[[NR:.*]] = "llvm.xor"(%[[NEX]], %[[NY]]) : (i32, i32) -> i32
// CHECK:      "func.return"(%[[NR]]) : (i32) -> ()
