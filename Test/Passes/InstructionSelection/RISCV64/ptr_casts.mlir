// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// The pass leaves `llvm.inttoptr` and `llvm.ptrtoint` alone.

"builtin.module"() ({
    "func.func"()  <{"function_type" = (i64) -> (i64), "sym_name" = "a"}> ({
    ^bb0(%a: i64):
        %p = "llvm.inttoptr"(%a) : (i64) -> !llvm.ptr
        // CHECK: %{{.*}} = "llvm.inttoptr"(%{{.*}}) : (i64) -> !llvm.ptr
        %b = "llvm.ptrtoint"(%p) : (!llvm.ptr) -> i64
        // CHECK-NEXT: %{{.*}} = "llvm.ptrtoint"(%{{.*}}) : (!llvm.ptr) -> i64
        "func.return"(%b) : (i64) -> ()
    }) : () -> ()
}) : () -> ()
