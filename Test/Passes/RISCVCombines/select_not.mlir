// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `select (not c), x, y` is `select c, y, x`: folding the not into swapped arms.

"builtin.module"() ({
  "func.func"() <{function_type = (i1, i32, i32) -> i32, sym_name = "foo"}> ({
  ^bb0(%c: i1, %x: i32, %y: i32):
    %m1 = "llvm.mlir.constant"() <{value = -1 : i1}> : () -> i1
    %nc = "llvm.xor"(%c, %m1) : (i1, i1) -> i1
    %r = "llvm.select"(%nc, %x, %y) : (i1, i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // Negative case: the condition is not a `not` (xor with -1), so the pattern does not fire.
  "func.func"() <{function_type = (i1, i32, i32) -> i32, sym_name = "bar"}> ({
  ^bb0(%c: i1, %x: i32, %y: i32):
    %r = "llvm.select"(%c, %x, %y) : (i1, i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// The not is folded away and the arms are swapped: select c, y, x.
// CHECK:      ^{{.*}}(%[[C:.*]] : i1, %[[X:.*]] : i32, %[[Y:.*]] : i32):
// CHECK:      %[[R:.*]] = "llvm.select"(%[[C]], %[[Y]], %[[X]]) : (i1, i32, i32) -> i32
// CHECK:      "func.return"(%[[R]]) : (i32) -> ()

// Plain condition: the select is unchanged.
// CHECK:      ^{{.*}}(%[[NC:.*]] : i1, %[[NX:.*]] : i32, %[[NY:.*]] : i32):
// CHECK:      %[[NR:.*]] = "llvm.select"(%[[NC]], %[[NX]], %[[NY]]) : (i1, i32, i32) -> i32
// CHECK:      "func.return"(%[[NR]]) : (i32) -> ()
