// RUN: veir-opt %s -p=riscv | filecheck %s

// `and x, 2^k - 1` keeps the low `k` bits without materializing the mask: zext.h for k = 16,
// zext.w for k = 32, and a slli/srli pair by 64 - k otherwise.

"builtin.module"() ({
    "func.func"() <{function_type = (i64) -> i64, sym_name = "zexth"}> ({
    ^bb(%a: i64):
        %c = "llvm.mlir.constant"() <{value = 65535 : i64}> : () -> i64
        %r = "llvm.and"(%a, %c) : (i64, i64) -> i64
        // CHECK:      "riscv.zexth"
        "func.return"(%r) : (i64) -> ()
    }) : () -> ()

    "func.func"() <{function_type = (i64) -> i64, sym_name = "zextw"}> ({
    ^bb(%a: i64):
        %c = "llvm.mlir.constant"() <{value = 4294967295 : i64}> : () -> i64
        %r = "llvm.and"(%a, %c) : (i64, i64) -> i64
        // CHECK:      "riscv.zextw"
        "func.return"(%r) : (i64) -> ()
    }) : () -> ()

    "func.func"() <{function_type = (i64) -> i64, sym_name = "shifts"}> ({
    ^bb(%a: i64):
        %c = "llvm.mlir.constant"() <{value = 1048575 : i64}> : () -> i64
        %r = "llvm.and"(%a, %c) : (i64, i64) -> i64
        // CHECK:      "riscv.slli"(%{{.*}}) <{"value" = 44 : i64}>
        // CHECK-NEXT: "riscv.srli"(%{{.*}}) <{"value" = 44 : i64}>
        "func.return"(%r) : (i64) -> ()
    }) : () -> ()
}) : () -> ()
