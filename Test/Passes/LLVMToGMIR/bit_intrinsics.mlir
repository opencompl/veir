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
    %smax = "llvm.intr.smax"(%x, %x) : (i32, i32) -> i32
    // CHECK-NEXT: "gmir.g_smax"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    %smin = "llvm.intr.smin"(%x, %x) : (i32, i32) -> i32
    // CHECK-NEXT: "gmir.g_smin"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    %umax = "llvm.intr.umax"(%x, %x) : (i32, i32) -> i32
    // CHECK-NEXT: "gmir.g_umax"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    %umin = "llvm.intr.umin"(%x, %x) : (i32, i32) -> i32
    // CHECK-NEXT: "gmir.g_umin"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    %abs = "llvm.intr.abs"(%x) <{is_int_min_poison = false}> : (i32) -> i32
    // CHECK-NEXT: "gmir.g_abs"(%{{.*}}) : (i32) -> i32
    // An `abs` whose minimum value is poison becomes the defined `abs`, which refines it.
    %abs_poison = "llvm.intr.abs"(%x) <{is_int_min_poison = true}> : (i32) -> i32
    // CHECK-NEXT: "gmir.g_abs"(%{{.*}}) : (i32) -> i32
    %saddsat = "llvm.intr.sadd.sat"(%x, %x) : (i32, i32) -> i32
    // CHECK-NEXT: "gmir.g_saddsat"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    %uaddsat = "llvm.intr.uadd.sat"(%x, %x) : (i32, i32) -> i32
    // CHECK-NEXT: "gmir.g_uaddsat"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    %ssubsat = "llvm.intr.ssub.sat"(%x, %x) : (i32, i32) -> i32
    // CHECK-NEXT: "gmir.g_ssubsat"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    %usubsat = "llvm.intr.usub.sat"(%x, %x) : (i32, i32) -> i32
    // CHECK-NEXT: "gmir.g_usubsat"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    %sshlsat = "llvm.intr.sshl.sat"(%x, %x) : (i32, i32) -> i32
    // CHECK-NEXT: "gmir.g_sshlsat"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    %ushlsat = "llvm.intr.ushl.sat"(%x, %x) : (i32, i32) -> i32
    // CHECK-NEXT: "gmir.g_ushlsat"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    "test.test"(%ctlz, %ctlz_poison, %cttz, %ctpop, %bswap, %bitreverse) : (i32, i32, i32, i32, i32, i32) -> ()
    "test.test"(%smax, %smin, %umax, %umin, %abs, %abs_poison) : (i32, i32, i32, i32, i32, i32) -> ()
    "test.test"(%saddsat, %uaddsat, %ssubsat, %usubsat, %sshlsat, %ushlsat) : (i32, i32, i32, i32, i32, i32) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
