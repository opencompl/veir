// RUN: veir-opt %s -p=arith-to-llvm | filecheck %s

// arith.floordivsi expands (matching arith ExpandOps and the floordivsi
// interpreter case) to:
//   z = a sdiv b; (a != z*b) && (sign a != sign b) ? z - 1 : z
// implemented as `add z, -1`. UB comes from the unconditional sdiv.

"builtin.module"() ({
  "func.func"() <{function_type = (i32, i32) -> i32, sym_name = "main"}> ({
    ^bb0(%0 : i32, %1 : i32):
      %r = "arith.floordivsi"(%0, %1) : (i32, i32) -> i32
      "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      ^{{.*}}([[A:%.*]] : i32, [[B:%.*]] : i32):
// CHECK-NEXT:   [[ZERO:%.*]] = "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32
// CHECK-NEXT:   [[NEG1:%.*]] = "llvm.mlir.constant"() <{"value" = -1 : i32}> : () -> i32
// CHECK-NEXT:   [[Z:%.*]] = "llvm.sdiv"([[A]], [[B]]) : (i32, i32) -> i32
// CHECK-NEXT:   [[ZB:%.*]] = "llvm.mul"([[Z]], [[B]]) : (i32, i32) -> i32
// CHECK-NEXT:   [[NE:%.*]] = "llvm.icmp"([[A]], [[ZB]]) <{"predicate" = 1 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:   [[ANEG:%.*]] = "llvm.icmp"([[A]], [[ZERO]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:   [[BNEG:%.*]] = "llvm.icmp"([[B]], [[ZERO]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:   [[SNE:%.*]] = "llvm.icmp"([[ANEG]], [[BNEG]]) <{"predicate" = 1 : i64}> : (i1, i1) -> i1
// CHECK-NEXT:   [[COND:%.*]] = "llvm.and"([[NE]], [[SNE]]) : (i1, i1) -> i1
// CHECK-NEXT:   [[ZM1:%.*]] = "llvm.add"([[Z]], [[NEG1]]) : (i32, i32) -> i32
// CHECK-NEXT:   [[R:%.*]] = "llvm.select"([[COND]], [[ZM1]], [[Z]]) : (i1, i32, i32) -> i32
// CHECK-NEXT:   "func.return"([[R]]) : (i32) -> ()
// CHECK-NOT: "arith.
