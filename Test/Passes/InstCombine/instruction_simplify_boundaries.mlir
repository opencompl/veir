// RUN: veir-opt %s --print-op-generic -p='apply-patterns{bswap_shl_to_single_low_byte bswap_lshr_to_single_high_byte bswap_and_high_byte_to_lshr bswap_trunc_bswap_to_high_bytes fshl_i16_rotate8_to_bswap fshl_undef_lo_to_shl fshr_undef_hi_to_lshr fshl_undef_hi_to_lshr fshr_undef_lo_to_shl umin_nuw_shl_common_lhs_dist_nsw umax_nuw_shl_common_lhs_dist_nsw}' | filecheck %s

// Endpoint byte swaps, undef funnel inputs, and both-source NSW preservation.
"builtin.module"() ({
  "func.func"() <{sym_name = "bswap_shl_to_single_low_byte", function_type = (i16) -> i16}> ({
  ^bb0(%arg0: i16):
    %v0 = "llvm.mlir.constant"() <{value = 8 : i16}> : () -> i16
    %v1 = "llvm.shl"(%arg0, %v0) : (i16, i16) -> i16
    %v2 = "llvm.intr.bswap"(%v1) : (i16) -> i16
    "func.return"(%v2) : (i16) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "bswap_shl_to_single_low_byte"
  // CHECK: "value" = 255 : i16
  // CHECK: "llvm.and"
  // CHECK-NOT: "llvm.intr.bswap"
  // CHECK: "func.return"

  "func.func"() <{sym_name = "bswap_lshr_to_single_high_byte", function_type = (i16) -> i16}> ({
  ^bb0(%arg0: i16):
    %v0 = "llvm.mlir.constant"() <{value = 8 : i16}> : () -> i16
    %v1 = "llvm.lshr"(%arg0, %v0) : (i16, i16) -> i16
    %v2 = "llvm.intr.bswap"(%v1) : (i16) -> i16
    "func.return"(%v2) : (i16) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "bswap_lshr_to_single_high_byte"
  // CHECK: "value" = -256 : i16
  // CHECK: "llvm.and"
  // CHECK-NOT: "llvm.intr.bswap"
  // CHECK: "func.return"

  "func.func"() <{sym_name = "bswap_and_high_byte_to_lshr", function_type = (i16) -> i16}> ({
  ^bb0(%arg0: i16):
    %v0 = "llvm.mlir.constant"() <{value = 65280 : i16}> : () -> i16
    %v1 = "llvm.and"(%arg0, %v0) : (i16, i16) -> i16
    %v2 = "llvm.intr.bswap"(%v1) : (i16) -> i16
    "func.return"(%v2) : (i16) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "bswap_and_high_byte_to_lshr"
  // CHECK: "value" = 8 : i16
  // CHECK: "llvm.lshr"
  // CHECK-NOT: "llvm.intr.bswap"
  // CHECK: "func.return"

  "func.func"() <{sym_name = "bswap_trunc_bswap_to_high_bytes", function_type = (i32) -> i16}> ({
  ^bb0(%arg0: i32):
    %v0 = "llvm.intr.bswap"(%arg0) : (i32) -> i32
    %v1 = "llvm.trunc"(%v0) : (i32) -> i16
    %v2 = "llvm.intr.bswap"(%v1) : (i16) -> i16
    "func.return"(%v2) : (i16) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "bswap_trunc_bswap_to_high_bytes"
  // CHECK: "value" = 16 : i32
  // CHECK: "llvm.lshr"
  // CHECK: "llvm.trunc"{{.*}}"overflowFlags" = 2 : i32
  // CHECK-NOT: "llvm.intr.bswap"
  // CHECK: "func.return"

  "func.func"() <{sym_name = "fshl_i16_rotate8_to_bswap", function_type = (i16) -> i16}> ({
  ^bb0(%arg0: i16):
    %v0 = "llvm.mlir.constant"() <{value = 8 : i16}> : () -> i16
    %v1 = "llvm.intr.fshl"(%arg0, %arg0, %v0) : (i16, i16, i16) -> i16
    "func.return"(%v1) : (i16) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "fshl_i16_rotate8_to_bswap"
  // CHECK: "llvm.intr.bswap"
  // CHECK-NOT: "llvm.intr.fshl"
  // CHECK: "func.return"

  "func.func"() <{sym_name = "fshl_undef_lo_to_shl", function_type = (i16) -> i16}> ({
  ^bb0(%arg0: i16):
    %v0 = "llvm.mlir.undef"() : () -> i16
    %v1 = "llvm.mlir.constant"() <{value = 3 : i16}> : () -> i16
    %v2 = "llvm.intr.fshl"(%arg0, %v0, %v1) : (i16, i16, i16) -> i16
    "func.return"(%v2) : (i16) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "fshl_undef_lo_to_shl"
  // CHECK: "value" = 3 : i16
  // CHECK: "llvm.shl"
  // CHECK-NOT: "llvm.intr.fshl"
  // CHECK: "func.return"

  "func.func"() <{sym_name = "fshr_undef_hi_to_lshr", function_type = (i16) -> i16}> ({
  ^bb0(%arg0: i16):
    %v0 = "llvm.mlir.undef"() : () -> i16
    %v1 = "llvm.mlir.constant"() <{value = 3 : i16}> : () -> i16
    %v2 = "llvm.intr.fshr"(%v0, %arg0, %v1) : (i16, i16, i16) -> i16
    "func.return"(%v2) : (i16) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "fshr_undef_hi_to_lshr"
  // CHECK: "value" = 3 : i16
  // CHECK: "llvm.lshr"
  // CHECK-NOT: "llvm.intr.fshr"
  // CHECK: "func.return"

  "func.func"() <{sym_name = "fshl_undef_hi_to_lshr", function_type = (i16) -> i16}> ({
  ^bb0(%arg0: i16):
    %v0 = "llvm.mlir.undef"() : () -> i16
    %v1 = "llvm.mlir.constant"() <{value = 3 : i16}> : () -> i16
    %v2 = "llvm.intr.fshl"(%v0, %arg0, %v1) : (i16, i16, i16) -> i16
    "func.return"(%v2) : (i16) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "fshl_undef_hi_to_lshr"
  // CHECK: "value" = 13 : i16
  // CHECK: "llvm.lshr"
  // CHECK-NOT: "llvm.intr.fshl"
  // CHECK: "func.return"

  "func.func"() <{sym_name = "fshr_undef_lo_to_shl", function_type = (i16) -> i16}> ({
  ^bb0(%arg0: i16):
    %v0 = "llvm.mlir.undef"() : () -> i16
    %v1 = "llvm.mlir.constant"() <{value = 3 : i16}> : () -> i16
    %v2 = "llvm.intr.fshr"(%arg0, %v0, %v1) : (i16, i16, i16) -> i16
    "func.return"(%v2) : (i16) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "fshr_undef_lo_to_shl"
  // CHECK: "value" = 13 : i16
  // CHECK: "llvm.shl"
  // CHECK-NOT: "llvm.intr.fshr"
  // CHECK: "func.return"

  "func.func"() <{sym_name = "umin_nuw_shl_common_lhs_dist_nsw", function_type = (i16, i16, i16) -> i16}> ({
  ^bb0(%arg0: i16, %arg1: i16, %arg2: i16):
    %v0 = "llvm.shl"(%arg0, %arg1) <{overflowFlags = 3 : i32}> : (i16, i16) -> i16
    %v1 = "llvm.shl"(%arg0, %arg2) <{overflowFlags = 3 : i32}> : (i16, i16) -> i16
    %v2 = "llvm.intr.umin"(%v0, %v1) : (i16, i16) -> i16
    "func.return"(%v2) : (i16) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "umin_nuw_shl_common_lhs_dist_nsw"
  // CHECK: "llvm.intr.umin"
  // CHECK: "llvm.shl"{{.*}}"overflowFlags" = 3 : i32
  // CHECK-NOT: "llvm.shl"
  // CHECK: "func.return"

  "func.func"() <{sym_name = "umax_nuw_shl_common_lhs_dist_nsw", function_type = (i16, i16, i16) -> i16}> ({
  ^bb0(%arg0: i16, %arg1: i16, %arg2: i16):
    %v0 = "llvm.shl"(%arg0, %arg1) <{overflowFlags = 3 : i32}> : (i16, i16) -> i16
    %v1 = "llvm.shl"(%arg0, %arg2) <{overflowFlags = 3 : i32}> : (i16, i16) -> i16
    %v2 = "llvm.intr.umax"(%v0, %v1) : (i16, i16) -> i16
    "func.return"(%v2) : (i16) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "umax_nuw_shl_common_lhs_dist_nsw"
  // CHECK: "llvm.intr.umax"
  // CHECK: "llvm.shl"{{.*}}"overflowFlags" = 3 : i32
  // CHECK-NOT: "llvm.shl"
  // CHECK: "func.return"

}) : () -> ()
