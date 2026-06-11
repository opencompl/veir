// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// Negative tests: these cases are not lowered, we leave them for future work.

"builtin.module"() ({
    "func.func"()  <{function_type = (!llvm.ptr, i32, i64) -> ()}> ({
    ^bb0(%p: !llvm.ptr, %i32: i32, %i: i64):
        // non-i64 index
        %a = "llvm.getelementptr"(%p, %i32) <{elem_type = i64, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i32) -> !llvm.ptr
        // CHECK: %{{.*}} = "llvm.getelementptr"(%{{.*}}, %{{.*}}) <{"elem_type" = i64, "noWrapFlags" = 0 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i32) -> !llvm.ptr

        // two dynamic indices
        %b = "llvm.getelementptr"(%p, %i, %i) <{elem_type = !llvm.array<10 x i8>, rawConstantIndices = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
        // CHECK-NEXT: %{{.*}} = "llvm.getelementptr"(%{{.*}}, %{{.*}}, %{{.*}}) <{"elem_type" = !llvm.array<10 x i8>, "noWrapFlags" = 0 : i32, "rawConstantIndices" = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr

        // single constant index
        %c = "llvm.getelementptr"(%p) <{elem_type = i64, rawConstantIndices = array<i32: 5>}> : (!llvm.ptr) -> !llvm.ptr
        // CHECK-NEXT: %{{.*}} = "llvm.getelementptr"(%{{.*}}) <{"elem_type" = i64, "noWrapFlags" = 0 : i32, "rawConstantIndices" = array<i32: 5>}> : (!llvm.ptr) -> !llvm.ptr

        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
