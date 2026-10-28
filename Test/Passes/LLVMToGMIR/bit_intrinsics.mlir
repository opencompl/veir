// RUN: veir-opt %s -p=llvm-to-gmir | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (i32) -> (), sym_name = "main"}> ({
  ^bb0(%x: i32):
    %ctlz = "llvm.intr.ctlz"(%x) <{is_zero_poison = false}> : (i32) -> i32
    // CHECK:      "gmir.g_ctlz"(%{{.*}}) : (i32) -> i32
    // A zero-poison count becomes the defined count, which refines it.
    %ctlz_poison = "llvm.intr.ctlz"(%x) <{is_zero_poison = true}> : (i32) -> i32
    // CHECK-NEXT: "gmir.g_ctlz"(%{{.*}}) : (i32) -> i32
    %cttz = "llvm.intr.cttz"(%x) <{is_zero_poison = true}> : (i32) -> i32
    // CHECK-NEXT: "gmir.g_cttz"(%{{.*}}) : (i32) -> i32
    %ctpop = "llvm.intr.ctpop"(%x) : (i32) -> i32
    // CHECK-NEXT: "gmir.g_ctpop"(%{{.*}}) : (i32) -> i32
    %bswap = "llvm.intr.bswap"(%x) : (i32) -> i32
    // CHECK-NEXT: "gmir.g_bswap"(%{{.*}}) : (i32) -> i32
    %bitreverse = "llvm.intr.bitreverse"(%x) : (i32) -> i32
    // CHECK-NEXT: "gmir.g_bitreverse"(%{{.*}}) : (i32) -> i32
    "test.test"(%ctlz, %ctlz_poison, %cttz, %ctpop, %bswap, %bitreverse) : (i32, i32, i32, i32, i32, i32) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
