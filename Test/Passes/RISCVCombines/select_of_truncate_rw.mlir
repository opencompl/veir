// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// A `trunc` of a `select` is pushed onto the select's arms:
// `trunc (select c, t, f) -> select c, (trunc t), (trunc f)`.

"builtin.module"() ({
  "func.func"() <{function_type = (i1, i64, i64) -> i32}> ({
  ^bb0(%c: i1, %t: i64, %f: i64):
    %s = "llvm.select"(%c, %t, %f) : (i1, i64, i64) -> i64
    %r = "llvm.trunc"(%s) : (i64) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // Negative case: the trunc feeds an add, not a select.
  "func.func"() <{function_type = (i64, i64) -> i32}> ({
  ^bb0(%a: i64, %b: i64):
    %s = "llvm.add"(%a, %b) : (i64, i64) -> i64
    %r = "llvm.trunc"(%s) : (i64) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// The trunc is distributed over both select arms.
// CHECK:      ^{{.*}}(%[[C:.*]] : i1, %[[T:.*]] : i64, %[[F:.*]] : i64):
// CHECK:      %[[TT:.*]] = "llvm.trunc"(%[[T]]) : (i64) -> i32
// CHECK:      %[[TF:.*]] = "llvm.trunc"(%[[F]]) : (i64) -> i32
// CHECK:      %[[SEL:.*]] = "llvm.select"(%[[C]], %[[TT]], %[[TF]]) : (i1, i32, i32) -> i32
// CHECK:      "func.return"(%[[SEL]]) : (i32) -> ()

// Not a select underneath: pattern does not fire.
// CHECK:      ^{{.*}}(%[[NA:.*]] : i64, %[[NB:.*]] : i64):
// CHECK:      %[[NADD:.*]] = "llvm.add"(%[[NA]], %[[NB]]) : (i64, i64) -> i64
// CHECK:      %[[NR:.*]] = "llvm.trunc"(%[[NADD]]) : (i64) -> i32
// CHECK:      "func.return"(%[[NR]]) : (i32) -> ()
