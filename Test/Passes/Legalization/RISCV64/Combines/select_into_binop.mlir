// RUN: veir-opt %s -p=prelegalizer-combiner-riscv64 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (i1, i32) -> (), sym_name = "chains_into_constants"}> ({
  ^bb0(%c: i1, %x: i32):
    %k = "gmir.g_constant"() <{value = 16 : i32}> : () -> i32
    // c ? (shl nuw x, 16) : x -> shl x, (shl (zext c), 4), dropping the flags.
    // CHECK-LABEL: func.func @chains_into_constants
    // CHECK:      %[[E:.*]] = "gmir.g_zext"(%{{.*}}) : (i1) -> i32
    // CHECK-NEXT: %[[K:.*]] = "gmir.g_constant"() <{"value" = 4 : i32}> : () -> i32
    // CHECK-NEXT: %[[A:.*]] = "gmir.g_shl"(%[[E]], %[[K]]) : (i32, i32) -> i32
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_shl"(%{{.*}}, %[[A]]) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[R]])
    %shl = "gmir.g_shl"(%x, %k) <{nuw}> : (i32, i32) -> i32
    %r = "gmir.g_select"(%c, %shl, %x) : (i1, i32, i32) -> i32
    "test.test"(%r) : (i32) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
