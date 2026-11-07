// RUN: veir-opt %s -p=prelegalizer-combiner-riscv64 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (i1) -> (), sym_name = "folds"}> ({
  ^bb0(%c: i1):
    %zero = "gmir.g_constant"() <{value = 0 : i32}> : () -> i32
    %one = "gmir.g_constant"() <{value = 1 : i32}> : () -> i32
    %m1 = "gmir.g_constant"() <{value = -1 : i32}> : () -> i32
    %six = "gmir.g_constant"() <{value = 6 : i32}> : () -> i32
    %seven = "gmir.g_constant"() <{value = 7 : i32}> : () -> i32
    %sixteen = "gmir.g_constant"() <{value = 16 : i32}> : () -> i32
    %min = "gmir.g_constant"() <{value = -2147483648 : i32}> : () -> i32
    %max = "gmir.g_constant"() <{value = 2147483647 : i32}> : () -> i32

    // c ? 1 : 0 -> zext c
    // CHECK:      %[[R:.*]] = "gmir.g_zext"(%[[C:.*]]) : (i1) -> i32
    // CHECK-NEXT: "test.test"(%[[R]])
    %r0 = "gmir.g_select"(%c, %one, %zero) : (i1, i32, i32) -> i32
    "test.test"(%r0) : (i32) -> ()

    // c ? -1 : 0 -> sext c
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_sext"(%[[C]]) : (i1) -> i32
    // CHECK-NEXT: "test.test"(%[[R]])
    %r1 = "gmir.g_select"(%c, %m1, %zero) : (i1, i32, i32) -> i32
    "test.test"(%r1) : (i32) -> ()

    // c ? 0 : 1 -> zext (not c)
    // CHECK-NEXT: %[[ONES:.*]] = "gmir.g_constant"() <{"value" = true}> : () -> i1
    // CHECK-NEXT: %[[NOT:.*]] = "gmir.g_xor"(%[[C]], %[[ONES]]) : (i1, i1) -> i1
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_zext"(%[[NOT]]) : (i1) -> i32
    // CHECK-NEXT: "test.test"(%[[R]])
    %r2 = "gmir.g_select"(%c, %zero, %one) : (i1, i32, i32) -> i32
    "test.test"(%r2) : (i32) -> ()

    // c ? 0 : -1 -> sext (not c)
    // CHECK-NEXT: %[[ONES:.*]] = "gmir.g_constant"() <{"value" = true}> : () -> i1
    // CHECK-NEXT: %[[NOT:.*]] = "gmir.g_xor"(%[[C]], %[[ONES]]) : (i1, i1) -> i1
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_sext"(%[[NOT]]) : (i1) -> i32
    // CHECK-NEXT: "test.test"(%[[R]])
    %r3 = "gmir.g_select"(%c, %zero, %m1) : (i1, i32, i32) -> i32
    "test.test"(%r3) : (i32) -> ()

    // c ? C : C - 1 -> add (zext c), C - 1
    // CHECK-NEXT: %[[E:.*]] = "gmir.g_zext"(%[[C]]) : (i1) -> i32
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_add"(%[[E]], %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[R]])
    %r4 = "gmir.g_select"(%c, %seven, %six) : (i1, i32, i32) -> i32
    "test.test"(%r4) : (i32) -> ()

    // c ? C : C + 1 -> add (sext c), C + 1
    // CHECK-NEXT: %[[E:.*]] = "gmir.g_sext"(%[[C]]) : (i1) -> i32
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_add"(%[[E]], %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[R]])
    %r5 = "gmir.g_select"(%c, %six, %seven) : (i1, i32, i32) -> i32
    "test.test"(%r5) : (i32) -> ()

    // The offset wraps at the width of the type: INT_MIN - 1 is INT_MAX.
    // CHECK-NEXT: %[[E:.*]] = "gmir.g_zext"(%[[C]]) : (i1) -> i32
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_add"(%[[E]], %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[R]])
    %r6 = "gmir.g_select"(%c, %min, %max) : (i1, i32, i32) -> i32
    "test.test"(%r6) : (i32) -> ()

    // c ? 2^k : 0 -> shl (zext c), k
    // CHECK-NEXT: %[[E:.*]] = "gmir.g_zext"(%[[C]]) : (i1) -> i32
    // CHECK-NEXT: %[[K:.*]] = "gmir.g_constant"() <{"value" = 4 : i32}> : () -> i32
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_shl"(%[[E]], %[[K]]) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[R]])
    %r7 = "gmir.g_select"(%c, %sixteen, %zero) : (i1, i32, i32) -> i32
    "test.test"(%r7) : (i32) -> ()

    // The sign bit is a power of two when read as an unsigned integer.
    // CHECK-NEXT: %[[E:.*]] = "gmir.g_zext"(%[[C]]) : (i1) -> i32
    // CHECK-NEXT: %[[K:.*]] = "gmir.g_constant"() <{"value" = 31 : i32}> : () -> i32
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_shl"(%[[E]], %[[K]]) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[R]])
    %r8 = "gmir.g_select"(%c, %min, %zero) : (i1, i32, i32) -> i32
    "test.test"(%r8) : (i32) -> ()

    // c ? 0 : 2^k -> shl (zext (not c)), k
    // CHECK-NEXT: %[[ONES:.*]] = "gmir.g_constant"() <{"value" = true}> : () -> i1
    // CHECK-NEXT: %[[NOT:.*]] = "gmir.g_xor"(%[[C]], %[[ONES]]) : (i1, i1) -> i1
    // CHECK-NEXT: %[[E:.*]] = "gmir.g_zext"(%[[NOT]]) : (i1) -> i32
    // CHECK-NEXT: %[[K:.*]] = "gmir.g_constant"() <{"value" = 4 : i32}> : () -> i32
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_shl"(%[[E]], %[[K]]) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[R]])
    %r9 = "gmir.g_select"(%c, %zero, %sixteen) : (i1, i32, i32) -> i32
    "test.test"(%r9) : (i32) -> ()

    // c ? -1 : C -> or (sext c), C
    // CHECK-NEXT: %[[E:.*]] = "gmir.g_sext"(%[[C]]) : (i1) -> i32
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_or"(%[[E]], %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[R]])
    %r10 = "gmir.g_select"(%c, %m1, %six) : (i1, i32, i32) -> i32
    "test.test"(%r10) : (i32) -> ()

    // c ? C : -1 -> or (sext (not c)), C
    // CHECK-NEXT: %[[ONES:.*]] = "gmir.g_constant"() <{"value" = true}> : () -> i1
    // CHECK-NEXT: %[[NOT:.*]] = "gmir.g_xor"(%[[C]], %[[ONES]]) : (i1, i1) -> i1
    // CHECK-NEXT: %[[E:.*]] = "gmir.g_sext"(%[[NOT]]) : (i1) -> i32
    // CHECK-NEXT: %[[K:.*]] = "gmir.g_constant"() <{"value" = 6 : i32}> : () -> i32
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_or"(%[[E]], %[[K]]) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[R]])
    %r11 = "gmir.g_select"(%c, %six, %m1) : (i1, i32, i32) -> i32
    "test.test"(%r11) : (i32) -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{function_type = (i1, i64, i32) -> (), sym_name = "no_folds"}> ({
  ^bb0(%c: i1, %wide: i64, %x: i32):
    %five = "gmir.g_constant"() <{value = 5 : i32}> : () -> i32
    %nine = "gmir.g_constant"() <{value = 9 : i32}> : () -> i32
    %zero = "gmir.g_constant"() <{value = 0 : i32}> : () -> i32
    %one = "gmir.g_constant"() <{value = 1 : i32}> : () -> i32
    %t1 = "gmir.g_constant"() <{value = 1 : i1}> : () -> i1
    %f1 = "gmir.g_constant"() <{value = 0 : i1}> : () -> i1
    %one128 = "gmir.g_constant"() <{value = 1 : i128}> : () -> i128
    %zero128 = "gmir.g_constant"() <{value = 0 : i128}> : () -> i128

    // Constants that no fold applies to.
    // CHECK-LABEL: func.func @no_folds
    // CHECK-NOT:   g_zext
    // CHECK-NOT:   g_sext
    // CHECK:       "gmir.g_select"(%{{.*}}, %{{.*}}, %{{.*}}) : (i1, i32, i32) -> i32
    %r0 = "gmir.g_select"(%c, %five, %nine) : (i1, i32, i32) -> i32
    "test.test"(%r0) : (i32) -> ()

    // A value that is not a constant.
    // CHECK:       "gmir.g_select"(%{{.*}}, %{{.*}}, %{{.*}}) : (i1, i32, i32) -> i32
    %r1 = "gmir.g_select"(%c, %x, %zero) : (i1, i32, i32) -> i32
    "test.test"(%r1) : (i32) -> ()

    // A condition wider than `i1`, where any nonzero value is true: `zext` would be wrong.
    // CHECK:       "gmir.g_select"(%{{.*}}, %{{.*}}, %{{.*}}) : (i64, i32, i32) -> i32
    %r2 = "gmir.g_select"(%wide, %one, %zero) : (i64, i32, i32) -> i32
    "test.test"(%r2) : (i32) -> ()

    // `i1` values: `zext` would not widen them.
    // CHECK:       "gmir.g_select"(%{{.*}}, %{{.*}}, %{{.*}}) : (i1, i1, i1) -> i1
    %r3 = "gmir.g_select"(%c, %t1, %f1) : (i1, i1, i1) -> i1
    "test.test"(%r3) : (i1) -> ()

    // Values wider than 64 bits: the legalizer does not lower their extensions.
    // CHECK:       "gmir.g_select"(%{{.*}}, %{{.*}}, %{{.*}}) : (i1, i128, i128) -> i128
    %r4 = "gmir.g_select"(%c, %one128, %zero128) : (i1, i128, i128) -> i128
    "test.test"(%r4) : (i128) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
