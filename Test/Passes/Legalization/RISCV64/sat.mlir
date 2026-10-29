// RUN: veir-opt %s -p=legalize-riscv64 | filecheck %s

// As in LLVM's GlobalISel, the saturating operations are lowered with min and max where those are
// legal (`i64`, with Zbb), and with an overflowing operation and a `g_select` otherwise. Compare
// with LLVM's `test/CodeGen/RISCV/GlobalISel/legalizer/legalize-sat-rv64.mir`.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64) -> (), sym_name = "minmax64"}> ({
  ^bb0(%x: i64, %y: i64):
    // CHECK-LABEL: func.func @minmax64
    // uadd.sat(x, y) = x + umin(~x, y)
    %uaddsat = "gmir.g_uaddsat"(%x, %y) : (i64, i64) -> i64
    // CHECK:      %[[ALLONES:.*]] = "gmir.g_constant"() <{"value" = -1 : i64}> : () -> i64
    // CHECK-NEXT: %[[NOT:.*]] = "gmir.g_xor"(%[[X:.*]], %[[ALLONES]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[MIN:.*]] = "gmir.g_umin"(%[[NOT]], %[[Y:.*]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[UADDSAT:.*]] = "gmir.g_add"(%[[X]], %[[MIN]]) : (i64, i64) -> i64
    // usub.sat(x, y) = x - umin(x, y)
    %usubsat = "gmir.g_usubsat"(%x, %y) : (i64, i64) -> i64
    // CHECK:      %[[MIN:.*]] = "gmir.g_umin"(%[[X]], %[[Y]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[USUBSAT:.*]] = "gmir.g_sub"(%[[X]], %[[MIN]]) : (i64, i64) -> i64
    // sadd.sat(x, y) = x + smin(smax(INT_MIN - smin(x, 0), y), INT_MAX - smax(x, 0))
    %saddsat = "gmir.g_saddsat"(%x, %y) : (i64, i64) -> i64
    // CHECK:      %[[MAX:.*]] = "gmir.g_constant"() <{"value" = 9223372036854775807 : i64}> : () -> i64
    // CHECK-NEXT: %[[MIN:.*]] = "gmir.g_constant"() <{"value" = -9223372036854775808 : i64}> : () -> i64
    // CHECK-NEXT: %[[ZERO:.*]] = "gmir.g_constant"() <{"value" = 0 : i64}> : () -> i64
    // CHECK-NEXT: %[[SMAX:.*]] = "gmir.g_smax"(%[[X]], %[[ZERO]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[HI:.*]] = "gmir.g_sub"(%[[MAX]], %[[SMAX]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[SMIN:.*]] = "gmir.g_smin"(%[[X]], %[[ZERO]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[LO:.*]] = "gmir.g_sub"(%[[MIN]], %[[SMIN]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[CLAMP:.*]] = "gmir.g_smax"(%[[LO]], %[[Y]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[CLAMPED:.*]] = "gmir.g_smin"(%[[CLAMP]], %[[HI]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[SADDSAT:.*]] = "gmir.g_add"(%[[X]], %[[CLAMPED]]) : (i64, i64) -> i64
    // ssub.sat(x, y) = x - smin(smax(smax(x, -1) - INT_MAX, y), smin(x, -1) - INT_MIN)
    %ssubsat = "gmir.g_ssubsat"(%x, %y) : (i64, i64) -> i64
    // CHECK:      %[[MAX:.*]] = "gmir.g_constant"() <{"value" = 9223372036854775807 : i64}> : () -> i64
    // CHECK-NEXT: %[[MIN:.*]] = "gmir.g_constant"() <{"value" = -9223372036854775808 : i64}> : () -> i64
    // CHECK-NEXT: %[[NEGONE:.*]] = "gmir.g_constant"() <{"value" = -1 : i64}> : () -> i64
    // CHECK-NEXT: %[[SMAX:.*]] = "gmir.g_smax"(%[[X]], %[[NEGONE]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[LO:.*]] = "gmir.g_sub"(%[[SMAX]], %[[MAX]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[SMIN:.*]] = "gmir.g_smin"(%[[X]], %[[NEGONE]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[HI:.*]] = "gmir.g_sub"(%[[SMIN]], %[[MIN]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[CLAMP:.*]] = "gmir.g_smax"(%[[LO]], %[[Y]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[CLAMPED:.*]] = "gmir.g_smin"(%[[CLAMP]], %[[HI]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[SSUBSAT:.*]] = "gmir.g_sub"(%[[X]], %[[CLAMPED]]) : (i64, i64) -> i64
    "test.test"(%uaddsat, %usubsat, %saddsat, %ssubsat) : (i64, i64, i64, i64) -> ()
    // CHECK: "test.test"(%[[UADDSAT]], %[[USUBSAT]], %[[SADDSAT]], %[[SSUBSAT]])
    "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{function_type = (i32, i32) -> (), sym_name = "addo32"}> ({
  ^bb0(%x: i32, %y: i32):
    // CHECK-LABEL: func.func @addo32
    // uadd.sat(x, y) = uaddo(x, y).carry ? -1 : x + y. The carry is `x + y <u y`.
    %uaddsat = "gmir.g_uaddsat"(%x, %y) : (i32, i32) -> i32
    // CHECK:      %[[SUM:.*]] = "riscv.addw"
    // CHECK:      %[[SUM32:.*]] = "builtin.unrealized_conversion_cast"(%[[SUM]]) : (!riscv.reg) -> i32
    // CHECK-NEXT: %[[L:.*]] = "gmir.g_sext"(%[[SUM32]]) : (i32) -> i64
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_sext"(%[[Y:.*]]) : (i32) -> i64
    // CHECK-NEXT: %[[CARRY:.*]] = "gmir.g_icmp"(%[[L]], %[[R]]) <{"predicate" = 6 : i64}> : (i64, i64) -> i64
    // CHECK-NEXT: %[[ALLONES:.*]] = "gmir.g_constant"() <{"value" = -1 : i64}> : () -> i64
    // CHECK-NEXT: %[[ALLONES32:.*]] = "gmir.g_trunc"(%[[ALLONES]]) : (i64) -> i32
    // CHECK-NEXT: %[[UADDSAT:.*]] = "gmir.g_select"(%[[CARRY]], %[[ALLONES32]], %[[SUM32]]) : (i64, i32, i32) -> i32
    // usub.sat(x, y) = usubo(x, y).borrow ? 0 : x - y. The borrow is `x <u y`.
    %usubsat = "gmir.g_usubsat"(%x, %y) : (i32, i32) -> i32
    // CHECK:      %[[DIFF:.*]] = "riscv.subw"
    // CHECK:      %[[DIFF32:.*]] = "builtin.unrealized_conversion_cast"(%[[DIFF]]) : (!riscv.reg) -> i32
    // CHECK-NEXT: %[[L:.*]] = "gmir.g_sext"(%[[X:.*]]) : (i32) -> i64
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_sext"(%[[Y]]) : (i32) -> i64
    // CHECK-NEXT: %[[BORROW:.*]] = "gmir.g_icmp"(%[[L]], %[[R]]) <{"predicate" = 6 : i64}> : (i64, i64) -> i64
    // CHECK-NEXT: %[[ZERO:.*]] = "gmir.g_constant"() <{"value" = 0 : i64}> : () -> i64
    // CHECK-NEXT: %[[ZERO32:.*]] = "gmir.g_trunc"(%[[ZERO]]) : (i64) -> i32
    // CHECK-NEXT: %[[USUBSAT:.*]] = "gmir.g_select"(%[[BORROW]], %[[ZERO32]], %[[DIFF32]]) : (i64, i32, i32) -> i32
    // sadd.sat(x, y) = saddo(x, y).overflow ? (sum >>s 31) + INT_MIN : sum. `g_saddo` is widened, and
    // overflows if the wide sum does not fit in `i32`.
    %saddsat = "gmir.g_saddsat"(%x, %y) : (i32, i32) -> i32
    // CHECK:      %[[L:.*]] = "gmir.g_sext"(%[[X]]) : (i32) -> i64
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_sext"(%[[Y]]) : (i32) -> i64
    // CHECK-NEXT: %[[WIDE:.*]] = "gmir.g_add"(%[[L]], %[[R]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[SUM:.*]] = "gmir.g_trunc"(%[[WIDE]]) : (i64) -> i32
    // CHECK-NEXT: %[[EXT:.*]] = "gmir.g_sext"(%[[SUM]]) : (i32) -> i64
    // CHECK-NEXT: %[[OV:.*]] = "gmir.g_icmp"(%[[WIDE]], %[[EXT]]) <{"predicate" = 1 : i64}> : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_constant"() <{"value" = 31 : i64}> : () -> i64
    // CHECK:      "riscv.sraw"
    // CHECK:      "gmir.g_constant"() <{"value" = -2147483648 : i64}> : () -> i64
    // CHECK:      "riscv.addw"
    // CHECK:      %[[SAT:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i32
    // CHECK-NEXT: %[[SADDSAT:.*]] = "gmir.g_select"(%[[OV]], %[[SAT]], %[[SUM]]) : (i64, i32, i32) -> i32
    %ssubsat = "gmir.g_ssubsat"(%x, %y) : (i32, i32) -> i32
    // CHECK:      %[[L:.*]] = "gmir.g_sext"(%[[X]]) : (i32) -> i64
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_sext"(%[[Y]]) : (i32) -> i64
    // CHECK-NEXT: %[[WIDE:.*]] = "gmir.g_sub"(%[[L]], %[[R]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[DIFF:.*]] = "gmir.g_trunc"(%[[WIDE]]) : (i64) -> i32
    // CHECK-NEXT: %[[EXT:.*]] = "gmir.g_sext"(%[[DIFF]]) : (i32) -> i64
    // CHECK-NEXT: %[[OV:.*]] = "gmir.g_icmp"(%[[WIDE]], %[[EXT]]) <{"predicate" = 1 : i64}> : (i64, i64) -> i64
    // CHECK:      "riscv.sraw"
    // CHECK:      "riscv.addw"
    // CHECK:      %[[SAT:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i32
    // CHECK-NEXT: %[[SSUBSAT:.*]] = "gmir.g_select"(%[[OV]], %[[SAT]], %[[DIFF]]) : (i64, i32, i32) -> i32
    "test.test"(%uaddsat, %usubsat, %saddsat, %ssubsat) : (i32, i32, i32, i32) -> ()
    // CHECK: "test.test"(%[[UADDSAT]], %[[USUBSAT]], %[[SADDSAT]], %[[SSUBSAT]])
    "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{function_type = (i8, i8) -> (), sym_name = "addo8"}> ({
  ^bb0(%x: i8, %y: i8):
    // CHECK-LABEL: func.func @addo8
    // The `i8` `g_select` is widened to `i32`, the narrowest legal width.
    %uaddsat = "gmir.g_uaddsat"(%x, %y) : (i8, i8) -> i8
    // CHECK:      %[[SUM:.*]] = "gmir.g_add"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
    // CHECK:      %[[CARRY:.*]] = "gmir.g_icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 6 : i64}> : (i64, i64) -> i64
    // CHECK:      %[[ALLONES:.*]] = "gmir.g_trunc"(%{{.*}}) : (i64) -> i32
    // CHECK-NEXT: %[[SUM32:.*]] = "gmir.g_trunc"(%[[SUM]]) : (i64) -> i32
    // CHECK-NEXT: %[[SEL:.*]] = "gmir.g_select"(%[[CARRY]], %[[ALLONES]], %[[SUM32]]) : (i64, i32, i32) -> i32
    // CHECK-NEXT: %[[UADDSAT:.*]] = "gmir.g_trunc"(%[[SEL]]) : (i32) -> i8
    "test.test"(%uaddsat) : (i8) -> ()
    // CHECK: "test.test"(%[[UADDSAT]])
    "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{function_type = (i64, i64, i32, i32) -> (), sym_name = "shl"}> ({
  ^bb0(%x: i64, %y: i64, %a: i32, %b: i32):
    // CHECK-LABEL: func.func @shl
    // sshl.sat(x, y) = x != (x << y) >>s y ? (x <s 0 ? INT_MIN : INT_MAX) : x << y
    %sshlsat = "gmir.g_sshlsat"(%x, %y) : (i64, i64) -> i64
    // CHECK:      %[[SHL:.*]] = "gmir.g_shl"(%[[X:.*]], %[[Y:.*]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[BACK:.*]] = "gmir.g_ashr"(%[[SHL]], %[[Y]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[MIN:.*]] = "gmir.g_constant"() <{"value" = -9223372036854775808 : i64}> : () -> i64
    // CHECK-NEXT: %[[MAX:.*]] = "gmir.g_constant"() <{"value" = 9223372036854775807 : i64}> : () -> i64
    // CHECK-NEXT: %[[ZERO:.*]] = "gmir.g_constant"() <{"value" = 0 : i64}> : () -> i64
    // CHECK-NEXT: %[[NEG:.*]] = "gmir.g_icmp"(%[[X]], %[[ZERO]]) <{"predicate" = 2 : i64}> : (i64, i64) -> i64
    // CHECK-NEXT: %[[SAT:.*]] = "gmir.g_select"(%[[NEG]], %[[MIN]], %[[MAX]]) : (i64, i64, i64) -> i64
    // CHECK-NEXT: %[[OV:.*]] = "gmir.g_icmp"(%[[X]], %[[BACK]]) <{"predicate" = 1 : i64}> : (i64, i64) -> i64
    // CHECK-NEXT: %[[SSHLSAT:.*]] = "gmir.g_select"(%[[OV]], %[[SAT]], %[[SHL]]) : (i64, i64, i64) -> i64
    // ushl.sat(x, y) = x != (x << y) >>u y ? -1 : x << y
    %ushlsat = "gmir.g_ushlsat"(%x, %y) : (i64, i64) -> i64
    // CHECK-NEXT: %[[SHL:.*]] = "gmir.g_shl"(%[[X]], %[[Y]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[BACK:.*]] = "gmir.g_lshr"(%[[SHL]], %[[Y]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[ALLONES:.*]] = "gmir.g_constant"() <{"value" = -1 : i64}> : () -> i64
    // CHECK-NEXT: %[[OV:.*]] = "gmir.g_icmp"(%[[X]], %[[BACK]]) <{"predicate" = 1 : i64}> : (i64, i64) -> i64
    // CHECK-NEXT: %[[USHLSAT:.*]] = "gmir.g_select"(%[[OV]], %[[ALLONES]], %[[SHL]]) : (i64, i64, i64) -> i64
    // The `i32` shifts are custom-legalized to the word shifts.
    %sshlsat32 = "gmir.g_sshlsat"(%a, %b) : (i32, i32) -> i32
    // CHECK:      "riscv.sllw"
    // CHECK:      "riscv.sraw"
    // CHECK:      %[[SAT:.*]] = "gmir.g_select"(%{{.*}}, %{{.*}}, %{{.*}}) : (i64, i32, i32) -> i32
    // CHECK:      %[[SSHLSAT32:.*]] = "gmir.g_select"(%{{.*}}, %[[SAT]], %{{.*}}) : (i64, i32, i32) -> i32
    "test.test"(%sshlsat, %ushlsat, %sshlsat32) : (i64, i64, i32) -> ()
    // CHECK: "test.test"(%[[SSHLSAT]], %[[USHLSAT]], %[[SSHLSAT32]])
    "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{function_type = (i64, i64, i32, i32, i1, i8, i8) -> (), sym_name = "parts"}> ({
  ^bb0(%x: i64, %y: i64, %a: i32, %b: i32, %c: i1, %p: i8, %q: i8):
    // CHECK-LABEL: func.func @parts
    // The sum overflows if it is smaller than `x` exactly when `y` is not negative.
    %saddo, %saddo_ov = "gmir.g_saddo"(%x, %y) : (i64, i64) -> (i64, i1)
    // CHECK:      %[[SUM:.*]] = "gmir.g_add"(%[[X:.*]], %[[Y:.*]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[ZERO:.*]] = "gmir.g_constant"() <{"value" = 0 : i64}> : () -> i64
    // CHECK-NEXT: %[[LT:.*]] = "gmir.g_icmp"(%[[SUM]], %[[X]]) <{"predicate" = 2 : i64}> : (i64, i64) -> i64
    // CHECK-NEXT: %[[NEG:.*]] = "gmir.g_icmp"(%[[Y]], %[[ZERO]]) <{"predicate" = 2 : i64}> : (i64, i64) -> i64
    // CHECK-NEXT: %[[XOR:.*]] = "gmir.g_xor"(%[[NEG]], %[[LT]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[SADDO_OV:.*]] = "gmir.g_trunc"(%[[XOR]]) : (i64) -> i1
    // The `i32` `g_ssubo` is widened.
    %ssubo, %ssubo_ov = "gmir.g_ssubo"(%a, %b) : (i32, i32) -> (i32, i1)
    // CHECK-NEXT: %[[L:.*]] = "gmir.g_sext"(%{{.*}}) : (i32) -> i64
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_sext"(%{{.*}}) : (i32) -> i64
    // CHECK-NEXT: %[[WIDE:.*]] = "gmir.g_sub"(%[[L]], %[[R]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[SSUBO:.*]] = "gmir.g_trunc"(%[[WIDE]]) : (i64) -> i32
    // CHECK-NEXT: %[[EXT:.*]] = "gmir.g_sext"(%[[SSUBO]]) : (i32) -> i64
    // CHECK-NEXT: %[[NE:.*]] = "gmir.g_icmp"(%[[WIDE]], %[[EXT]]) <{"predicate" = 1 : i64}> : (i64, i64) -> i64
    // CHECK-NEXT: %[[SSUBO_OV:.*]] = "gmir.g_trunc"(%[[NE]]) : (i64) -> i1
    %uaddo, %uaddo_ov = "gmir.g_uaddo"(%x, %y) : (i64, i64) -> (i64, i1)
    // CHECK-NEXT: %[[UADDO:.*]] = "gmir.g_add"(%[[X]], %[[Y]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[ULT:.*]] = "gmir.g_icmp"(%[[UADDO]], %[[Y]]) <{"predicate" = 6 : i64}> : (i64, i64) -> i64
    // CHECK-NEXT: %[[UADDO_OV:.*]] = "gmir.g_trunc"(%[[ULT]]) : (i64) -> i1
    %usubo, %usubo_ov = "gmir.g_usubo"(%x, %y) : (i64, i64) -> (i64, i1)
    // CHECK-NEXT: %[[USUBO:.*]] = "gmir.g_sub"(%[[X]], %[[Y]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[ULT:.*]] = "gmir.g_icmp"(%[[X]], %[[Y]]) <{"predicate" = 6 : i64}> : (i64, i64) -> i64
    // CHECK-NEXT: %[[USUBO_OV:.*]] = "gmir.g_trunc"(%[[ULT]]) : (i64) -> i1
    // The values of an `i8` `g_select` are widened to `i32`, and its condition, whose high bits
    // matter, is zero-extended to `i64`.
    %select = "gmir.g_select"(%c, %p, %q) : (i1, i8, i8) -> i8
    // CHECK-NEXT: %[[P:.*]] = "gmir.g_anyext"(%{{.*}}) : (i8) -> i32
    // CHECK-NEXT: %[[Q:.*]] = "gmir.g_anyext"(%{{.*}}) : (i8) -> i32
    // CHECK-NEXT: %[[C:.*]] = "gmir.g_anyext"(%{{.*}}) : (i1) -> i64
    // CHECK-NEXT: %[[ONE:.*]] = "gmir.g_constant"() <{"value" = 1 : i64}> : () -> i64
    // CHECK-NEXT: %[[MASKED:.*]] = "gmir.g_and"(%[[C]], %[[ONE]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[SEL:.*]] = "gmir.g_select"(%[[MASKED]], %[[P]], %[[Q]]) : (i64, i32, i32) -> i32
    // CHECK-NEXT: %[[SELECT:.*]] = "gmir.g_trunc"(%[[SEL]]) : (i32) -> i8
    "test.test"(%saddo, %saddo_ov, %ssubo, %ssubo_ov, %uaddo, %uaddo_ov, %usubo, %usubo_ov, %select) : (i64, i1, i32, i1, i64, i1, i64, i1, i8) -> ()
    // CHECK-NEXT: "test.test"(%[[SUM]], %[[SADDO_OV]], %[[SSUBO]], %[[SSUBO_OV]], %[[UADDO]], %[[UADDO_OV]], %[[USUBO]], %[[USUBO_OV]], %[[SELECT]])
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
