// RUN: veir-opt -p=legalize %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i32}> ({
    %lhs = "llvm.mlir.constant"() <{ "value" = 3 : i32 }> : () -> i32
    %rhs = "llvm.mlir.constant"() <{ "value" = 5 : i32 }> : () -> i32
    %x = "llvm.add"(%lhs, %rhs) : (i32, i32) -> i32
// CHECK:      %[[lhs:.*]] = "llvm.zext"(%{{.*}}) : (i32) -> i64
// CHECK-NEXT: %[[rhs:.*]] = "llvm.zext"(%{{.*}}) : (i32) -> i64
// CHECK-NEXT: %[[res:.*]] = "llvm.add"(%[[lhs]], %[[rhs]]) : (i64, i64) -> i64
// CHECK-NEXT: %[[trunc:.*]] = "llvm.trunc"(%[[res]]) : (i64) -> i32
    "func.return"(%x) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
