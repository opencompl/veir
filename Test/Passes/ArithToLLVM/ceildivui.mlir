// RUN: veir-opt %s -p=arith-to-llvm | filecheck %s

// arith.ceildivui expands (matching arith ExpandOps and the ceildivui interpreter
// case) to: a == 0 ? 0 : ((a - 1) udiv b) + 1. The divide-by-zero / poison-divisor
// UB comes from the unconditional udiv.

"builtin.module"() ({
  "func.func"() <{function_type = (i32, i32) -> i32, sym_name = "main"}> ({
    ^bb0(%0 : i32, %1 : i32):
      %r = "arith.ceildivui"(%0, %1) : (i32, i32) -> i32
      "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      ^{{.*}}([[A:%.*]] : i32, [[B:%.*]] : i32):
// CHECK-NEXT:   [[ZERO:%.*]] = "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32
// CHECK-NEXT:   [[ONE:%.*]] = "llvm.mlir.constant"() <{"value" = 1 : i32}> : () -> i32
// CHECK-NEXT:   [[ISZ:%.*]] = "llvm.icmp"([[A]], [[ZERO]]) <{"predicate" = 0 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:   [[AM1:%.*]] = "llvm.sub"([[A]], [[ONE]]) : (i32, i32) -> i32
// CHECK-NEXT:   [[Q:%.*]] = "llvm.udiv"([[AM1]], [[B]]) : (i32, i32) -> i32
// CHECK-NEXT:   [[QP1:%.*]] = "llvm.add"([[Q]], [[ONE]]) : (i32, i32) -> i32
// CHECK-NEXT:   [[R:%.*]] = "llvm.select"([[ISZ]], [[ZERO]], [[QP1]]) : (i1, i32, i32) -> i32
// CHECK-NEXT:   "func.return"([[R]]) : (i32) -> ()
// CHECK-NOT: "arith.
