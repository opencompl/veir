// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// A `zext` of a `select` is pushed onto the select's arms:
// `zext (select c, t, f) -> select c, (zext t), (zext f)`.

"builtin.module"() ({
  "func.func"() <{function_type = (i1, i32, i32) -> i64, sym_name = "foo"}> ({
  ^bb0(%c: i1, %t: i32, %f: i32):
    %s = "llvm.select"(%c, %t, %f) : (i1, i32, i32) -> i32
    %z = "llvm.zext"(%s) : (i32) -> i64
    "func.return"(%z) : (i64) -> ()
  }) : () -> ()

  // Negative case: the zext feeds an add, not a select.
  "func.func"() <{function_type = (i32, i32) -> i64, sym_name = "bar"}> ({
  ^bb0(%a: i32, %b: i32):
    %s = "llvm.add"(%a, %b) : (i32, i32) -> i32
    %z = "llvm.zext"(%s) : (i32) -> i64
    "func.return"(%z) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// The zext is distributed over both select arms.
// CHECK:      ^{{.*}}(%[[C:.*]] : i1, %[[T:.*]] : i32, %[[F:.*]] : i32):
// CHECK:      %[[ZT:.*]] = "llvm.zext"(%[[T]]) : (i32) -> i64
// CHECK:      %[[ZF:.*]] = "llvm.zext"(%[[F]]) : (i32) -> i64
// CHECK:      %[[SEL:.*]] = "llvm.select"(%[[C]], %[[ZT]], %[[ZF]]) : (i1, i64, i64) -> i64
// CHECK:      "func.return"(%[[SEL]]) : (i64) -> ()

// Not a select underneath: pattern does not fire.
// CHECK:      ^{{.*}}(%[[NA:.*]] : i32, %[[NB:.*]] : i32):
// CHECK:      %[[NADD:.*]] = "llvm.add"(%[[NA]], %[[NB]]) : (i32, i32) -> i32
// CHECK:      %[[NZ:.*]] = "llvm.zext"(%[[NADD]]) : (i32) -> i64
// CHECK:      "func.return"(%[[NZ]]) : (i64) -> ()
