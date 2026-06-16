// RUN: veir-opt %s -p=cse | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (!llvm.ptr, i64)>}> ({
^bb0(%base : !llvm.ptr, %idx : i64):
    %g0 = "llvm.getelementptr"(%base, %idx) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %g1 = "llvm.getelementptr"(%base, %idx) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    // the ones bellow are different and should not be eliminated
    %g_d0 = "llvm.getelementptr"(%base, %idx) <{"elem_type" = i64, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %g_d1 = "llvm.getelementptr"(%base, %idx) <{"elem_type" = i32, "noWrapFlags" = 0 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "test.test"(%g0, %g1, %g_d0, %g_d1) : (!llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()

    // CHECK-LABEL: ^{{.*}}(%{{.*}} : !llvm.ptr, %{{.*}} : i64):
    // CHECK-NEXT: %[[G0:.*]] = "llvm.getelementptr"(%{{.*}}, %{{.*}}) <{"elem_type" = i32, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    // CHECK-NEXT: %[[GD0:.*]] = "llvm.getelementptr"(%{{.*}}, %{{.*}}) <{"elem_type" = i64, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    // CHECK-NEXT: %[[GD1:.*]] = "llvm.getelementptr"(%{{.*}}, %{{.*}}) <{"elem_type" = i32, "noWrapFlags" = 0 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    // CHECK-NEXT: "test.test"(%[[G0]], %[[G0]], %[[GD0]], %[[GD1]]) : (!llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
