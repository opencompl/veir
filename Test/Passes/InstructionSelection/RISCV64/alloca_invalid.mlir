// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// Negative tests: these allocas are left alone.

"builtin.module"() ({
    "llvm.func"() <{sym_name = "foo", function_type = !llvm.func<void (i64)>}> ({
    ^bb0(%n: i64):
        %c1 = "llvm.mlir.constant"() <{ "value" = 1 : i64 }> : () -> i64

        // A dynamic element count has no static frame-object size.
        %a = "llvm.alloca"(%n) <{ elem_type = i64 }> : (i64) -> !llvm.ptr
        // CHECK: %{{.*}} = "llvm.alloca"(%{{.*}}) <{"alignment" = 0 : i64, "elem_type" = i64}> : (i64) -> !llvm.ptr

        // `inalloca` is a calling-convention marker with no `riscv_stack` equivalent.
        %b = "llvm.alloca"(%c1) <{ elem_type = i64, inalloca }> : (i64) -> !llvm.ptr
        // CHECK: %{{.*}} = "llvm.alloca"(%{{.*}}) <{"alignment" = 0 : i64, "elem_type" = i64, inalloca}> : (i64) -> !llvm.ptr

        // `riscv_stack.alloca` requires a power-of-two alignment; `llvm.alloca` does not.
        %c = "llvm.alloca"(%c1) <{ elem_type = i64, alignment = 3 : i64 }> : (i64) -> !llvm.ptr
        // CHECK: %{{.*}} = "llvm.alloca"(%{{.*}}) <{"alignment" = 3 : i64, "elem_type" = i64}> : (i64) -> !llvm.ptr

        // An element type of unknown size.
        %d = "llvm.alloca"(%c1) <{ elem_type = !llvm.func<i64 ()> }> : (i64) -> !llvm.ptr
        // CHECK: %{{.*}} = "llvm.alloca"(%{{.*}}) <{"alignment" = 0 : i64, "elem_type" = !llvm.func<i64 ()>}> : (i64) -> !llvm.ptr

        "test.test"(%a) : (!llvm.ptr) -> ()
        "test.test"(%b) : (!llvm.ptr) -> ()
        "test.test"(%c) : (!llvm.ptr) -> ()
        "test.test"(%d) : (!llvm.ptr) -> ()
        "llvm.br"()[^bb1] : () -> ()

    ^bb1():
        // Outside the entry block: this op may execute more than once, so it does not
        // name a single stack slot.
        %e = "llvm.alloca"(%c1) <{ elem_type = i64 }> : (i64) -> !llvm.ptr
        // CHECK: %{{.*}} = "llvm.alloca"(%{{.*}}) <{"alignment" = 0 : i64, "elem_type" = i64}> : (i64) -> !llvm.ptr
        "test.test"(%e) : (!llvm.ptr) -> ()
        "llvm.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
