// RUN: veir-opt %s -p=instcombine | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (i8, i16) -> (i8, i8, i8, i8, i64, i8, i8, i8), sym_name = "foo"}> ({
  ^bb0(%x: i8, %s: i16):
    %m1 = "llvm.mlir.constant"() <{value = -1 : i8}> : () -> i8
    %c8 = "llvm.mlir.constant"() <{value = 8 : i8}> : () -> i8
    %c128 = "llvm.mlir.constant"() <{value = -128 : i8}> : () -> i8
    %c6 = "llvm.mlir.constant"() <{value = 6 : i8}> : () -> i8
    // x * -1 => 0 - x, keeping nsw and dropping nuw.
    %neg = "llvm.mul"(%x, %m1) <{overflowFlags = 3 : i32}> : (i8, i8) -> i8
    // x urem 8 => x & 7, and x urem 128 (the constant -128 as i8) => x & 127.
    %rem8 = "llvm.urem"(%x, %c8) : (i8, i8) -> i8
    %rem128 = "llvm.urem"(%x, %c128) : (i8, i8) -> i8
    // Negative case: 6 is not a power of two.
    %rem6 = "llvm.urem"(%x, %c6) : (i8, i8) -> i8
    // sext (sext x) => sext x.
    %s32 = "llvm.sext"(%s) : (i16) -> i32
    %s64 = "llvm.sext"(%s32) : (i32) -> i64
    // bitreverse (bitreverse x) => x.
    %r1 = "llvm.intr.bitreverse"(%x) : (i8) -> i8
    %r2 = "llvm.intr.bitreverse"(%r1) : (i8) -> i8
    // smax x, x => x and umin x, x => x.
    %smax = "llvm.intr.smax"(%x, %x) : (i8, i8) -> i8
    %umin = "llvm.intr.umin"(%x, %x) : (i8, i8) -> i8
    "func.return"(%neg, %rem8, %rem128, %rem6, %s64, %r2, %smax, %umin) : (i8, i8, i8, i8, i64, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: func.func @foo
// CHECK-SAME:  (%[[X:.*]]: i8, %[[S:.*]]: i16)
// CHECK-DAG:   %[[ZERO:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i8}> : () -> i8
// CHECK-DAG:   %[[NEG:.*]] = "llvm.sub"(%[[ZERO]], %[[X]]) <{"overflowFlags" = 1 : i32}> : (i8, i8) -> i8
// CHECK-DAG:   %[[M7:.*]] = "llvm.mlir.constant"() <{"value" = 7 : i8}> : () -> i8
// CHECK-DAG:   %[[REM8:.*]] = "llvm.and"(%[[X]], %[[M7]]) : (i8, i8) -> i8
// CHECK-DAG:   %[[M127:.*]] = "llvm.mlir.constant"() <{"value" = 127 : i8}> : () -> i8
// CHECK-DAG:   %[[REM128:.*]] = "llvm.and"(%[[X]], %[[M127]]) : (i8, i8) -> i8
// CHECK-DAG:   %[[REM6:.*]] = "llvm.urem"(%[[X]], %{{.*}}) : (i8, i8) -> i8
// CHECK-DAG:   %[[S64:.*]] = "llvm.sext"(%[[S]]) : (i16) -> i64
// CHECK:       "func.return"(%[[NEG]], %[[REM8]], %[[REM128]], %[[REM6]], %[[S64]], %[[X]], %[[X]], %[[X]])
