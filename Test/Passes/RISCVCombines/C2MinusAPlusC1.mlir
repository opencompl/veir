// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// C2 - (A + C1) → (C2 - C1) - A: the two constants combine into a single
// constant, leaving one subtract of A.

"builtin.module"() ({
  "func.func"() <{function_type = (i64) -> i64, sym_name = "foo"}> ({
  ^bb0(%a: i64):
    %c1 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %c2 = "llvm.mlir.constant"() <{value = 10 : i64}> : () -> i64
    %add = "llvm.add"(%a, %c1) : (i64, i64) -> i64
    %r = "llvm.sub"(%c2, %add) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: the minuend is not a constant, so no fold.
  "func.func"() <{function_type = (i64, i64) -> i64, sym_name = "bar"}> ({
  ^bb0(%a: i64, %y: i64):
    %c1 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %add = "llvm.add"(%a, %c1) : (i64, i64) -> i64
    %r = "llvm.sub"(%y, %add) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: the added operand is not a constant, so no fold.
  "func.func"() <{function_type = (i64, i64) -> i64, sym_name = "baz"}> ({
  ^bb0(%a: i64, %x: i64):
    %c2 = "llvm.mlir.constant"() <{value = 10 : i64}> : () -> i64
    %add = "llvm.add"(%a, %x) : (i64, i64) -> i64
    %r = "llvm.sub"(%c2, %add) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// Folds to (10 - 3) - A = 7 - A.
// CHECK:      ^{{.*}}(%[[A:.*]] : i64):
// CHECK:      %[[C:.*]] = "llvm.mlir.constant"(){{.*}}value{{.*}}= 7 : i64{{.*}} : () -> i64
// CHECK:      %[[R:.*]] = "llvm.sub"(%[[C]], %[[A]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[R]]) : (i64) -> ()

// Non-constant minuend: the pattern does not fire.
// CHECK:      ^{{.*}}(%[[NA:.*]] : i64, %[[NY:.*]] : i64):
// CHECK:      %[[NADD:.*]] = "llvm.add"(%[[NA]], %{{.*}}) : (i64, i64) -> i64
// CHECK:      %[[NR:.*]] = "llvm.sub"(%[[NY]], %[[NADD]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[NR]]) : (i64) -> ()

// Non-constant addend: the pattern does not fire.
// CHECK:      ^{{.*}}(%[[MA:.*]] : i64, %[[MX:.*]] : i64):
// CHECK:      %[[MADD:.*]] = "llvm.add"(%[[MA]], %[[MX]]) : (i64, i64) -> i64
// CHECK:      %[[MR:.*]] = "llvm.sub"(%{{.*}}, %[[MADD]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[MR]]) : (i64) -> ()
