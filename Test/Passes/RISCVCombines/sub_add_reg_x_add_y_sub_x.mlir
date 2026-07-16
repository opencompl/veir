// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `(x + y) - x` cancels the `+ x`/`- x` pair and simplifies to `y`. The `sub`
// is erased and its uses forwarded to `y`.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64) -> i64, sym_name = "foo"}> ({
  ^bb0(%x: i64, %y: i64):
    %add = "llvm.add"(%x, %y) : (i64, i64) -> i64
    %s = "llvm.sub"(%add, %x) : (i64, i64) -> i64
    "func.return"(%s) : (i64) -> ()
  }) : () -> ()

  // Negative case: the subtrahend is not the `add`'s first operand, so no fold.
  "func.func"() <{function_type = (i64, i64, i64) -> i64, sym_name = "bar"}> ({
  ^bb0(%x: i64, %y: i64, %w: i64):
    %add = "llvm.add"(%x, %y) : (i64, i64) -> i64
    %s = "llvm.sub"(%add, %w) : (i64, i64) -> i64
    "func.return"(%s) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// The `sub` is gone; `y` is returned directly (the dead `add` may remain).
// CHECK:      ^{{.*}}(%{{.*}} : i64, %[[Y:.*]] : i64):
// CHECK-NOT:  "llvm.sub"
// CHECK:      "func.return"(%[[Y]]) : (i64) -> ()

// Unrelated subtrahend: the `sub` survives.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i64, %[[NY:.*]] : i64, %[[NW:.*]] : i64):
// CHECK:      %[[NADD:.*]] = "llvm.add"(%[[NX]], %[[NY]]) : (i64, i64) -> i64
// CHECK:      %[[NSUB:.*]] = "llvm.sub"(%[[NADD]], %[[NW]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[NSUB]]) : (i64) -> ()
