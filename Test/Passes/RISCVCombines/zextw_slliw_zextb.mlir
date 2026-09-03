// RUN: veir-opt %s -p=riscv-combine | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg, sym_name = "byte_shift"}> ({
  ^bb0(%x : !riscv.reg):
    %zextb = "riscv.zextb"(%x) : (!riscv.reg) -> !riscv.reg
    %zextw = "riscv.zextw"(%zextb) : (!riscv.reg) -> !riscv.reg
    %slliw = "riscv.slliw"(%zextw) <{"value" = 24 : i64}> : (!riscv.reg) -> !riscv.reg
    %out = "riscv.zextw"(%slliw) : (!riscv.reg) -> !riscv.reg
    "func.return"(%out) : (!riscv.reg) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg, sym_name = "shift_too_large"}> ({
  ^bb0(%x : !riscv.reg):
    %zextb = "riscv.zextb"(%x) : (!riscv.reg) -> !riscv.reg
    %slliw = "riscv.slliw"(%zextb) <{"value" = 25 : i64}> : (!riscv.reg) -> !riscv.reg
    %out = "riscv.zextw"(%slliw) : (!riscv.reg) -> !riscv.reg
    "func.return"(%out) : (!riscv.reg) -> ()
  }) : () -> ()

  // Cover every statically instantiated Puddle pattern for the valid shift range.
  "func.func"() <{function_type = (!riscv.reg) -> (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg), sym_name = "all_byte_shifts"}> ({
  ^bb0(%x : !riscv.reg):
    %zextb = "riscv.zextb"(%x) : (!riscv.reg) -> !riscv.reg
    %slliw0 = "riscv.slliw"(%zextb) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
    %out0 = "riscv.zextw"(%slliw0) : (!riscv.reg) -> !riscv.reg
    %slliw1 = "riscv.slliw"(%zextb) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
    %out1 = "riscv.zextw"(%slliw1) : (!riscv.reg) -> !riscv.reg
    %slliw2 = "riscv.slliw"(%zextb) <{"value" = 2 : i64}> : (!riscv.reg) -> !riscv.reg
    %out2 = "riscv.zextw"(%slliw2) : (!riscv.reg) -> !riscv.reg
    %slliw3 = "riscv.slliw"(%zextb) <{"value" = 3 : i64}> : (!riscv.reg) -> !riscv.reg
    %out3 = "riscv.zextw"(%slliw3) : (!riscv.reg) -> !riscv.reg
    %slliw4 = "riscv.slliw"(%zextb) <{"value" = 4 : i64}> : (!riscv.reg) -> !riscv.reg
    %out4 = "riscv.zextw"(%slliw4) : (!riscv.reg) -> !riscv.reg
    %slliw5 = "riscv.slliw"(%zextb) <{"value" = 5 : i64}> : (!riscv.reg) -> !riscv.reg
    %out5 = "riscv.zextw"(%slliw5) : (!riscv.reg) -> !riscv.reg
    %slliw6 = "riscv.slliw"(%zextb) <{"value" = 6 : i64}> : (!riscv.reg) -> !riscv.reg
    %out6 = "riscv.zextw"(%slliw6) : (!riscv.reg) -> !riscv.reg
    %slliw7 = "riscv.slliw"(%zextb) <{"value" = 7 : i64}> : (!riscv.reg) -> !riscv.reg
    %out7 = "riscv.zextw"(%slliw7) : (!riscv.reg) -> !riscv.reg
    %slliw8 = "riscv.slliw"(%zextb) <{"value" = 8 : i64}> : (!riscv.reg) -> !riscv.reg
    %out8 = "riscv.zextw"(%slliw8) : (!riscv.reg) -> !riscv.reg
    %slliw9 = "riscv.slliw"(%zextb) <{"value" = 9 : i64}> : (!riscv.reg) -> !riscv.reg
    %out9 = "riscv.zextw"(%slliw9) : (!riscv.reg) -> !riscv.reg
    %slliw10 = "riscv.slliw"(%zextb) <{"value" = 10 : i64}> : (!riscv.reg) -> !riscv.reg
    %out10 = "riscv.zextw"(%slliw10) : (!riscv.reg) -> !riscv.reg
    %slliw11 = "riscv.slliw"(%zextb) <{"value" = 11 : i64}> : (!riscv.reg) -> !riscv.reg
    %out11 = "riscv.zextw"(%slliw11) : (!riscv.reg) -> !riscv.reg
    %slliw12 = "riscv.slliw"(%zextb) <{"value" = 12 : i64}> : (!riscv.reg) -> !riscv.reg
    %out12 = "riscv.zextw"(%slliw12) : (!riscv.reg) -> !riscv.reg
    %slliw13 = "riscv.slliw"(%zextb) <{"value" = 13 : i64}> : (!riscv.reg) -> !riscv.reg
    %out13 = "riscv.zextw"(%slliw13) : (!riscv.reg) -> !riscv.reg
    %slliw14 = "riscv.slliw"(%zextb) <{"value" = 14 : i64}> : (!riscv.reg) -> !riscv.reg
    %out14 = "riscv.zextw"(%slliw14) : (!riscv.reg) -> !riscv.reg
    %slliw15 = "riscv.slliw"(%zextb) <{"value" = 15 : i64}> : (!riscv.reg) -> !riscv.reg
    %out15 = "riscv.zextw"(%slliw15) : (!riscv.reg) -> !riscv.reg
    %slliw16 = "riscv.slliw"(%zextb) <{"value" = 16 : i64}> : (!riscv.reg) -> !riscv.reg
    %out16 = "riscv.zextw"(%slliw16) : (!riscv.reg) -> !riscv.reg
    %slliw17 = "riscv.slliw"(%zextb) <{"value" = 17 : i64}> : (!riscv.reg) -> !riscv.reg
    %out17 = "riscv.zextw"(%slliw17) : (!riscv.reg) -> !riscv.reg
    %slliw18 = "riscv.slliw"(%zextb) <{"value" = 18 : i64}> : (!riscv.reg) -> !riscv.reg
    %out18 = "riscv.zextw"(%slliw18) : (!riscv.reg) -> !riscv.reg
    %slliw19 = "riscv.slliw"(%zextb) <{"value" = 19 : i64}> : (!riscv.reg) -> !riscv.reg
    %out19 = "riscv.zextw"(%slliw19) : (!riscv.reg) -> !riscv.reg
    %slliw20 = "riscv.slliw"(%zextb) <{"value" = 20 : i64}> : (!riscv.reg) -> !riscv.reg
    %out20 = "riscv.zextw"(%slliw20) : (!riscv.reg) -> !riscv.reg
    %slliw21 = "riscv.slliw"(%zextb) <{"value" = 21 : i64}> : (!riscv.reg) -> !riscv.reg
    %out21 = "riscv.zextw"(%slliw21) : (!riscv.reg) -> !riscv.reg
    %slliw22 = "riscv.slliw"(%zextb) <{"value" = 22 : i64}> : (!riscv.reg) -> !riscv.reg
    %out22 = "riscv.zextw"(%slliw22) : (!riscv.reg) -> !riscv.reg
    %slliw23 = "riscv.slliw"(%zextb) <{"value" = 23 : i64}> : (!riscv.reg) -> !riscv.reg
    %out23 = "riscv.zextw"(%slliw23) : (!riscv.reg) -> !riscv.reg
    %slliw24 = "riscv.slliw"(%zextb) <{"value" = 24 : i64}> : (!riscv.reg) -> !riscv.reg
    %out24 = "riscv.zextw"(%slliw24) : (!riscv.reg) -> !riscv.reg
    "func.return"(%out0, %out1, %out2, %out3, %out4, %out5, %out6, %out7, %out8, %out9, %out10, %out11, %out12, %out13, %out14, %out15, %out16, %out17, %out18, %out19, %out20, %out21, %out22, %out23, %out24) : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()

  // The newly created `slli` must take the root's `x4` result type, not become
  // an unallocated `!riscv.reg` value.
  "func.func"() <{function_type = (!riscv.reg<x1>) -> !riscv.reg<x4>, sym_name = "typed_byte_shift"}> ({
  ^bb0(%x : !riscv.reg<x1>):
    %zextb = "riscv.zextb"(%x) : (!riscv.reg<x1>) -> !riscv.reg<x2>
    %slliw = "riscv.slliw"(%zextb) <{"value" = 24 : i64}> : (!riscv.reg<x2>) -> !riscv.reg<x3>
    %out = "riscv.zextw"(%slliw) : (!riscv.reg<x3>) -> !riscv.reg<x4>
    "func.return"(%out) : (!riscv.reg<x4>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: "sym_name" = "byte_shift"
// CHECK:      ^{{.*}}(%[[SHIFT_X:.*]] : !riscv.reg):
// CHECK-NEXT: %[[SHIFT_B:.*]] = "riscv.zextb"(%[[SHIFT_X]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: %[[SHIFT:.*]] = "riscv.slli"(%[[SHIFT_B]]) <{"value" = 24 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[SHIFT]]) : (!riscv.reg) -> ()

// CHECK-LABEL: "sym_name" = "shift_too_large"
// CHECK:      ^{{.*}}(%[[LARGE_X:.*]] : !riscv.reg):
// CHECK-NEXT: %[[LARGE_B:.*]] = "riscv.zextb"(%[[LARGE_X]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: %[[LARGE_SHIFT:.*]] = "riscv.slliw"(%[[LARGE_B]]) <{"value" = 25 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: %[[LARGE_OUT:.*]] = "riscv.zextw"(%[[LARGE_SHIFT]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[LARGE_OUT]]) : (!riscv.reg) -> ()

// CHECK-LABEL: "sym_name" = "all_byte_shifts"
// CHECK:      ^{{.*}}(%[[ALL_X:.*]] : !riscv.reg):
// CHECK-NEXT: %[[ALL_B:.*]] = "riscv.zextb"(%[[ALL_X]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: %{{.*}} = "riscv.slli"(%[[ALL_B]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: %{{.*}} = "riscv.slli"(%[[ALL_B]]) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: %{{.*}} = "riscv.slli"(%[[ALL_B]]) <{"value" = 2 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: %{{.*}} = "riscv.slli"(%[[ALL_B]]) <{"value" = 3 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: %{{.*}} = "riscv.slli"(%[[ALL_B]]) <{"value" = 4 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: %{{.*}} = "riscv.slli"(%[[ALL_B]]) <{"value" = 5 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: %{{.*}} = "riscv.slli"(%[[ALL_B]]) <{"value" = 6 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: %{{.*}} = "riscv.slli"(%[[ALL_B]]) <{"value" = 7 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: %{{.*}} = "riscv.slli"(%[[ALL_B]]) <{"value" = 8 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: %{{.*}} = "riscv.slli"(%[[ALL_B]]) <{"value" = 9 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: %{{.*}} = "riscv.slli"(%[[ALL_B]]) <{"value" = 10 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: %{{.*}} = "riscv.slli"(%[[ALL_B]]) <{"value" = 11 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: %{{.*}} = "riscv.slli"(%[[ALL_B]]) <{"value" = 12 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: %{{.*}} = "riscv.slli"(%[[ALL_B]]) <{"value" = 13 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: %{{.*}} = "riscv.slli"(%[[ALL_B]]) <{"value" = 14 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: %{{.*}} = "riscv.slli"(%[[ALL_B]]) <{"value" = 15 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: %{{.*}} = "riscv.slli"(%[[ALL_B]]) <{"value" = 16 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: %{{.*}} = "riscv.slli"(%[[ALL_B]]) <{"value" = 17 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: %{{.*}} = "riscv.slli"(%[[ALL_B]]) <{"value" = 18 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: %{{.*}} = "riscv.slli"(%[[ALL_B]]) <{"value" = 19 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: %{{.*}} = "riscv.slli"(%[[ALL_B]]) <{"value" = 20 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: %{{.*}} = "riscv.slli"(%[[ALL_B]]) <{"value" = 21 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: %{{.*}} = "riscv.slli"(%[[ALL_B]]) <{"value" = 22 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: %{{.*}} = "riscv.slli"(%[[ALL_B]]) <{"value" = 23 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: %{{.*}} = "riscv.slli"(%[[ALL_B]]) <{"value" = 24 : i64}> : (!riscv.reg) -> !riscv.reg

// CHECK-LABEL: "sym_name" = "typed_byte_shift"
// CHECK:      ^{{.*}}(%[[TYPED_SHIFT_X:.*]] : !riscv.reg<x1>):
// CHECK-NEXT: %[[TYPED_SHIFT_B:.*]] = "riscv.zextb"(%[[TYPED_SHIFT_X]]) : (!riscv.reg<x1>) -> !riscv.reg<x2>
// CHECK-NEXT: %[[TYPED_SHIFT:.*]] = "riscv.slli"(%[[TYPED_SHIFT_B]]) <{"value" = 24 : i64}> : (!riscv.reg<x2>) -> !riscv.reg<x4>
// CHECK-NEXT: "func.return"(%[[TYPED_SHIFT]]) : (!riscv.reg<x4>) -> ()
