// RUN: veir-opt %s -p=llvm-to-gmir,legalize-riscv64,isel-riscv64 | filecheck %s

// Negative tests: these cases are not lowered, we leave them for future work.

"builtin.module"() ({
    "func.func"()  <{function_type = (!llvm.ptr, i64) -> (), sym_name = "foo"}> ({
    ^bb0(%p: !llvm.ptr, %i: i64):
        // an index into a vector
        %b = "llvm.getelementptr"(%p, %i) <{elem_type = vector<4xi32>, rawConstantIndices = array<i32: 0, -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        // CHECK: %{{.*}} = "llvm.getelementptr"(%{{.*}}, %{{.*}}) <{"elem_type" = vector<4xi32>, "noWrapFlags" = 0 : i32, "rawConstantIndices" = array<i32: 0, -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr

        "test.test"(%b) : (!llvm.ptr) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
