// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
^bb0(%a: i32, %b: i32, %c: i64, %d: i8, %p: !llvm.ptr):
  %mul = "gmir.g_mul"(%a, %b) <{overflowFlags = 3 : i32}> : (i32, i32) -> i32
  %and = "gmir.g_and"(%a, %b) : (i32, i32) -> i32
  %or = "gmir.g_or"(%a, %b) <{isDisjoint}> : (i32, i32) -> i32
  %xor = "gmir.g_xor"(%a, %b) : (i32, i32) -> i32
  %sdiv = "gmir.g_sdiv"(%a, %b) <{isExact}> : (i32, i32) -> i32
  %udiv = "gmir.g_udiv"(%a, %b) <{isExact}> : (i32, i32) -> i32
  %srem = "gmir.g_srem"(%a, %b) : (i32, i32) -> i32
  %urem = "gmir.g_urem"(%a, %b) : (i32, i32) -> i32
  %shl = "gmir.g_shl"(%a, %c) <{overflowFlags = 1 : i32}> : (i32, i64) -> i32
  %lshr = "gmir.g_lshr"(%a, %d) <{isExact}> : (i32, i8) -> i32
  %ashr = "gmir.g_ashr"(%a, %b) : (i32, i32) -> i32
  %inttoptr = "gmir.g_inttoptr"(%c) : (i64) -> !llvm.ptr
  %ptrtoint = "gmir.g_ptrtoint"(%p) : (!llvm.ptr) -> i64
  %bswap = "gmir.g_bswap"(%a) : (i32) -> i32
  %bitreverse = "gmir.g_bitreverse"(%a) : (i32) -> i32
  %saddsat = "gmir.g_saddsat"(%a, %b) : (i32, i32) -> i32
  %uaddsat = "gmir.g_uaddsat"(%a, %b) : (i32, i32) -> i32
  %ssubsat = "gmir.g_ssubsat"(%a, %b) : (i32, i32) -> i32
  %usubsat = "gmir.g_usubsat"(%a, %b) : (i32, i32) -> i32
  %sshlsat = "gmir.g_sshlsat"(%a, %c) : (i32, i64) -> i32
  %ushlsat = "gmir.g_ushlsat"(%a, %b) : (i32, i32) -> i32
  %smin = "gmir.g_smin"(%a, %b) : (i32, i32) -> i32
  %smax = "gmir.g_smax"(%a, %b) : (i32, i32) -> i32
  %umin = "gmir.g_umin"(%a, %b) : (i32, i32) -> i32
  %umax = "gmir.g_umax"(%a, %b) : (i32, i32) -> i32
  %abs = "gmir.g_abs"(%a) : (i32) -> i32
  %ctlz = "gmir.g_ctlz"(%a) : (i32) -> i8
  %cttz = "gmir.g_cttz"(%a) : (i32) -> i32
  %ctpop = "gmir.g_ctpop"(%c) : (i64) -> i32
}) : () -> ()

// CHECK: "gmir.g_mul"(%{{.*}}, %{{.*}}) <{"overflowFlags" = 3 : i32}> : (i32, i32) -> i32
// CHECK: "gmir.g_and"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK: "gmir.g_or"(%{{.*}}, %{{.*}}) <{isDisjoint}> : (i32, i32) -> i32
// CHECK: "gmir.g_xor"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK: "gmir.g_sdiv"(%{{.*}}, %{{.*}}) <{isExact}> : (i32, i32) -> i32
// CHECK: "gmir.g_udiv"(%{{.*}}, %{{.*}}) <{isExact}> : (i32, i32) -> i32
// CHECK: "gmir.g_srem"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK: "gmir.g_urem"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK: "gmir.g_shl"(%{{.*}}, %{{.*}}) <{"overflowFlags" = 1 : i32}> : (i32, i64) -> i32
// CHECK: "gmir.g_lshr"(%{{.*}}, %{{.*}}) <{isExact}> : (i32, i8) -> i32
// CHECK: "gmir.g_ashr"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK: "gmir.g_inttoptr"(%{{.*}}) : (i64) -> !llvm.ptr
// CHECK: "gmir.g_ptrtoint"(%{{.*}}) : (!llvm.ptr) -> i64
// CHECK: "gmir.g_bswap"(%{{.*}}) : (i32) -> i32
// CHECK: "gmir.g_bitreverse"(%{{.*}}) : (i32) -> i32
// CHECK: "gmir.g_saddsat"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK: "gmir.g_uaddsat"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK: "gmir.g_ssubsat"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK: "gmir.g_usubsat"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK: "gmir.g_sshlsat"(%{{.*}}, %{{.*}}) : (i32, i64) -> i32
// CHECK: "gmir.g_ushlsat"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK: "gmir.g_smin"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK: "gmir.g_smax"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK: "gmir.g_umin"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK: "gmir.g_umax"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK: "gmir.g_abs"(%{{.*}}) : (i32) -> i32
// CHECK: "gmir.g_ctlz"(%{{.*}}) : (i32) -> i8
// CHECK: "gmir.g_cttz"(%{{.*}}) : (i32) -> i32
// CHECK: "gmir.g_ctpop"(%{{.*}}) : (i64) -> i32
