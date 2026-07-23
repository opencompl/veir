// RUN: veir-opt %s -p=arith-to-llvm | filecheck %s

// Like mulsi_extended, but the high half is unsigned: operands are zero-extended
// to 2*N bits (umulHigh in the mului_extended interpreter case).

"builtin.module"() ({
  "func.func"() <{function_type = (i32, i32) -> i32, sym_name = "main"}> ({
    ^bb0(%0 : i32, %1 : i32):
      %s:2 = "arith.mului_extended"(%0, %1) : (i32, i32) -> (i32, i32)
      "func.return"(%s#1) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      ^{{.*}}([[A:%.*]] : i32, [[B:%.*]] : i32):
// CHECK-NEXT:   [[LOW:%.*]] = "llvm.mul"([[A]], [[B]]) : (i32, i32) -> i32
// CHECK-NEXT:   [[AE:%.*]] = "llvm.zext"([[A]]) : (i32) -> i64
// CHECK-NEXT:   [[BE:%.*]] = "llvm.zext"([[B]]) : (i32) -> i64
// CHECK-NEXT:   [[WM:%.*]] = "llvm.mul"([[AE]], [[BE]]) : (i64, i64) -> i64
// CHECK-NEXT:   [[SH:%.*]] = "llvm.mlir.constant"() <{"value" = 32 : i64}> : () -> i64
// CHECK-NEXT:   [[HI:%.*]] = "llvm.lshr"([[WM]], [[SH]]) : (i64, i64) -> i64
// CHECK-NEXT:   [[HIGH:%.*]] = "llvm.trunc"([[HI]]) : (i64) -> i32
// CHECK-NEXT:   "func.return"([[HIGH]]) : (i32) -> ()
// CHECK-NOT: "arith.
