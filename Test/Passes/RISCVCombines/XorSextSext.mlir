// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// A sign extension distributes over `xor`: sign-extending the inputs then xoring is the same as xoring then sign-extending, because sign extension replicates the top bit uniformly. The two casts are hoisted through
// the bitwise op: `(sext X) xor (sext Y) -> sext (X xor Y)`, doing the
// bitwise op on the narrow operands and casting once.

"builtin.module"() ({
  "func.func"() <{function_type = (i32, i32) -> i64, sym_name = "foo"}> ({
  ^bb0(%x: i32, %y: i32):
    %ex = "llvm.sext"(%x) : (i32) -> i64
    %ey = "llvm.sext"(%y) : (i32) -> i64
    %r = "llvm.xor"(%ex, %ey) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: only one operand is a `sext`, so nothing is hoisted.
  "func.func"() <{function_type = (i32, i64) -> i64, sym_name = "bar"}> ({
  ^bb0(%x: i32, %y: i64):
    %ex = "llvm.sext"(%x) : (i32) -> i64
    %r = "llvm.xor"(%ex, %y) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// The bitwise op runs on the narrow operands, then a single `sext` widens.
// CHECK:      ^{{.*}}(%[[X:.*]] : i32, %[[Y:.*]] : i32):
// CHECK:      %[[OP:.*]] = "llvm.xor"(%[[X]], %[[Y]]) : (i32, i32) -> i32
// CHECK-NEXT: %[[E:.*]] = "llvm.sext"(%[[OP]]) : (i32) -> i64
// CHECK:      "func.return"(%[[E]]) : (i64) -> ()

// Single cast: the pattern does not fire.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i32, %[[NY:.*]] : i64):
// CHECK:      %[[NEX:.*]] = "llvm.sext"(%[[NX]]) : (i32) -> i64
// CHECK:      %[[NR:.*]] = "llvm.xor"(%[[NEX]], %[[NY]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[NR]]) : (i64) -> ()
