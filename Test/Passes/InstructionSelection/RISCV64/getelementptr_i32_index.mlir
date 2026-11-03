// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// isel expects LLVM-to-GMIR to have normalized GEP indices to i64; an i32 index is left alone.

"builtin.module"() ({
    "func.func"()  <{function_type = (!llvm.ptr, i32) -> (), sym_name = "foo"}> ({
    ^bb0(%p: !llvm.ptr, %i: i32):
        // CHECK: "llvm.getelementptr"
        %a = "llvm.getelementptr"(%p, %i) <{elem_type = i64, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i32) -> !llvm.ptr
        "test.test"(%a) : (!llvm.ptr) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
