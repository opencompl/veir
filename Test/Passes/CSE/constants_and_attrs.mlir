// RUN: veir-opt %s -p=cse | filecheck %s

"builtin.module"() ({
  "llvm.func"()  <{function_type = !llvm.func<void (i32, i32)>}> ({
^bb0(%arg0 : i32, %arg1 : i32):
    %c0_i32 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %c1_i32 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %c2_i32 = "llvm.mlir.constant"() <{value = 9 : i32}> : () -> i32
    %c0_i64 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    "test.test"(%c0_i32, %c1_i32, %c2_i32, %c0_i64) : (i32, i32, i32, i64) -> ()

    // CHECK-LABEL: ^{{.*}}(%{{.*}} : i32, %{{.*}} : i32):
    // CHECK-NEXT: %[[C7_I32:.*]] = "llvm.mlir.constant"() <{"value" = 7 : i32}> : () -> i32
    // CHECK-NEXT: %[[C9_I32:.*]] = "llvm.mlir.constant"() <{"value" = 9 : i32}> : () -> i32
    // CHECK-NEXT: %[[C7_I64:.*]] = "llvm.mlir.constant"() <{"value" = 7 : i64}> : () -> i64
    // CHECK-NEXT: "test.test"(%[[C7_I32]], %[[C7_I32]], %[[C9_I32]], %[[C7_I64]]) : (i32, i32, i32, i64) -> ()

    %add_attr0 = "llvm.add"(%arg0, %arg1) {"tag" = "keep"} : (i32, i32) -> i32
    %add_attr1 = "llvm.add"(%arg0, %arg1) {"tag" = "keep"} : (i32, i32) -> i32
    "test.test"(%add_attr0, %add_attr1) : (i32, i32) -> ()

    // CHECK-NEXT: %[[ADD_ATTR0:.*]] = "llvm.add"(%{{.*}}, %{{.*}}) {"tag" = "keep"} : (i32, i32) -> i32
    // CHECK-NEXT: %[[ADD_ATTR1:.*]] = "llvm.add"(%{{.*}}, %{{.*}}) {"tag" = "keep"} : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[ADD_ATTR0]], %[[ADD_ATTR1]]) : (i32, i32) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
