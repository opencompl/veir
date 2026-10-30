// RUN: veir-opt %s -p=llvm-to-gmir | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (i32, i32) -> (), sym_name = "main"}> ({
  ^bb0(%x: i32, %y: i32):
    %ctlz = "llvm.intr.ctlz"(%x) <{is_zero_poison = false}> : (i32) -> i32
    // CHECK:      "gmir.g_ctlz"(%{{.*}}) : (i32) -> i32
    // A count whose zero input is poison becomes a zero-poison count.
    %ctlz_poison = "llvm.intr.ctlz"(%x) <{is_zero_poison = true}> : (i32) -> i32
    // CHECK-NEXT: "gmir.g_ctlz_zero_poison"(%{{.*}}) : (i32) -> i32
    %cttz = "llvm.intr.cttz"(%x) <{is_zero_poison = false}> : (i32) -> i32
    // CHECK-NEXT: "gmir.g_cttz"(%{{.*}}) : (i32) -> i32
    %cttz_poison = "llvm.intr.cttz"(%x) <{is_zero_poison = true}> : (i32) -> i32
    // CHECK-NEXT: "gmir.g_cttz_zero_poison"(%{{.*}}) : (i32) -> i32
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
    %fshl = "llvm.intr.fshl"(%x, %y, %x) : (i32, i32, i32) -> i32
    // CHECK:      "gmir.g_fshl"(%{{.*}}, %{{.*}}, %{{.*}}) : (i32, i32, i32) -> i32
    %fshr = "llvm.intr.fshr"(%x, %y, %x) : (i32, i32, i32) -> i32
    // CHECK-NEXT: "gmir.g_fshr"(%{{.*}}, %{{.*}}, %{{.*}}) : (i32, i32, i32) -> i32
    // A funnel shift whose data operands are identical is a rotate.
    %rotl = "llvm.intr.fshl"(%x, %x, %y) : (i32, i32, i32) -> i32
    // CHECK-NEXT: "gmir.g_rotl"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    %rotr = "llvm.intr.fshr"(%x, %x, %y) : (i32, i32, i32) -> i32
    // CHECK-NEXT: "gmir.g_rotr"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    "test.test"(%smax, %smin, %umax, %umin, %abs, %abs_poison, %fshl, %fshr, %rotl, %rotr) : (i32, i32, i32, i32, i32, i32, i32, i32, i32, i32) -> ()
    "test.test"(%ctlz, %ctlz_poison, %cttz, %cttz_poison, %ctpop, %bswap, %bitreverse) : (i32, i32, i32, i32, i32, i32, i32) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
