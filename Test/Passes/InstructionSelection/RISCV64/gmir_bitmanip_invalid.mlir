// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// Illegal operations are not selected.
"builtin.module"() ({
  "func.func"() <{function_type = (i32) -> (), sym_name = "main"}> ({
  ^bb0(%x: i32):
    %ctlz = "gmir.g_ctlz"(%x) : (i32) -> i32
    // CHECK:      "gmir.g_ctlz"(%{{.*}}) : (i32) -> i32
    %ctpop = "gmir.g_ctpop"(%x) : (i32) -> i32
    // CHECK-NEXT: "gmir.g_ctpop"(%{{.*}}) : (i32) -> i32
    %bswap = "gmir.g_bswap"(%x) : (i32) -> i32
    // CHECK-NEXT: "gmir.g_bswap"(%{{.*}}) : (i32) -> i32
    %bitreverse = "gmir.g_bitreverse"(%x) : (i32) -> i32
    // CHECK-NEXT: "gmir.g_bitreverse"(%{{.*}}) : (i32) -> i32
    "test.test"(%ctlz, %ctpop, %bswap, %bitreverse) : (i32, i32, i32, i32) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
