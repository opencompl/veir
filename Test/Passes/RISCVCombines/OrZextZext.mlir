// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// A zero extension distributes over `or`: zero-extending the inputs then oring is the same as oring then zero-extending, because the added high bits are all zero. The two casts are hoisted through
// the bitwise op: `(zext X) or (zext Y) -> zext (X or Y)`, doing the
// bitwise op on the narrow operands and casting once.

"builtin.module"() ({
  "func.func"() <{function_type = (i32, i32) -> i64, sym_name = "foo"}> ({
  ^bb0(%x: i32, %y: i32):
    %ex = "llvm.zext"(%x) : (i32) -> i64
    %ey = "llvm.zext"(%y) : (i32) -> i64
    %r = "llvm.or"(%ex, %ey) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: only one operand is a `zext`, so nothing is hoisted.
  "func.func"() <{function_type = (i32, i64) -> i64, sym_name = "bar"}> ({
  ^bb0(%x: i32, %y: i64):
    %ex = "llvm.zext"(%x) : (i32) -> i64
    %r = "llvm.or"(%ex, %y) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// The bitwise op runs on the narrow operands, then a single `zext` widens.
// CHECK:      ^{{.*}}(%[[X:.*]] : i32, %[[Y:.*]] : i32):
// CHECK:      %[[OP:.*]] = "llvm.or"(%[[X]], %[[Y]]) : (i32, i32) -> i32
// CHECK-NEXT: %[[E:.*]] = "llvm.zext"(%[[OP]]) : (i32) -> i64
// CHECK:      "func.return"(%[[E]]) : (i64) -> ()

// Single cast: the pattern does not fire.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i32, %[[NY:.*]] : i64):
// CHECK:      %[[NEX:.*]] = "llvm.zext"(%[[NX]]) : (i32) -> i64
// CHECK:      %[[NR:.*]] = "llvm.or"(%[[NEX]], %[[NY]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[NR]]) : (i64) -> ()
