// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// `binop(C1, C2)` with two constant operands folds to a single constant: add,
// sub, mul, smin, smax and shl. As in LLVM, a shl by an amount out of range,
// which is poison, folds to 0.

"builtin.module"() ({
  // add(5, 7) = 12
  "func.func"() <{function_type = () -> i32, sym_name = "foo"}> ({
  ^bb0():
    %a = "gmir.g_constant"() <{value = 5 : i32}> : () -> i32
    %b = "gmir.g_constant"() <{value = 7 : i32}> : () -> i32
    %r = "gmir.g_add"(%a, %b) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // The folded i8 sum must wrap to the normalized value -128.
  "func.func"() <{function_type = () -> i8, sym_name = "add_wraps"}> ({
    %a = "gmir.g_constant"() <{value = 127 : i8}> : () -> i8
    %b = "gmir.g_constant"() <{value = 1 : i8}> : () -> i8
    %r = "gmir.g_add"(%a, %b) : (i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()

  // sub(20, 8) = 12
  "func.func"() <{function_type = () -> i32, sym_name = "bar"}> ({
  ^bb0():
    %a = "gmir.g_constant"() <{value = 20 : i32}> : () -> i32
    %b = "gmir.g_constant"() <{value = 8 : i32}> : () -> i32
    %r = "gmir.g_sub"(%a, %b) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // smin(4, 9) = 4
  "func.func"() <{function_type = () -> i32, sym_name = "baz"}> ({
  ^bb0():
    %a = "gmir.g_constant"() <{value = 4 : i32}> : () -> i32
    %b = "gmir.g_constant"() <{value = 9 : i32}> : () -> i32
    %r = "gmir.g_smin"(%a, %b) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // shl(1, 2) = 4
  "func.func"() <{function_type = () -> i32, sym_name = "shl"}> ({
  ^bb0():
    %a = "gmir.g_constant"() <{value = 1 : i32}> : () -> i32
    %b = "gmir.g_constant"() <{value = 2 : i32}> : () -> i32
    %r = "gmir.g_shl"(%a, %b) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // shl(1, 32) at i32 is out of range: 0
  "func.func"() <{function_type = () -> i32, sym_name = "shl_out_of_range"}> ({
  ^bb0():
    %a = "gmir.g_constant"() <{value = 1 : i32}> : () -> i32
    %b = "gmir.g_constant"() <{value = 32 : i32}> : () -> i32
    %r = "gmir.g_shl"(%a, %b) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// add folds to 12.
// CHECK:      func.func @foo() -> i32 {
// CHECK:      %[[R:.*]] = "gmir.g_constant"() <{"value" = 12 : i32}> : () -> i32
// CHECK:      "func.return"(%[[R]]) : (i32) -> ()

// The overflowing sum uses the normalized constant returned by the fold.
// CHECK-LABEL: func.func @add_wraps() -> i8 {
// CHECK: %[[WRAPPED:.*]] = "gmir.g_constant"() <{"value" = -128 : i8}> : () -> i8
// CHECK-NEXT: "func.return"(%[[WRAPPED]]) : (i8) -> ()

// sub folds to 12.
// CHECK:      func.func @bar() -> i32 {
// CHECK:      %[[R2:.*]] = "gmir.g_constant"() <{"value" = 12 : i32}> : () -> i32
// CHECK:      "func.return"(%[[R2]]) : (i32) -> ()

// smin folds to a constant (the smin op is gone).
// CHECK:      func.func @baz() -> i32 {
// CHECK-NOT:  "gmir.g_smin"
// CHECK:      "func.return"(%{{.*}}) : (i32) -> ()

// shl folds to 4.
// CHECK-LABEL: func.func @shl() -> i32 {
// CHECK-NEXT: %[[SHL:.*]] = "gmir.g_constant"() <{"value" = 4 : i32}> : () -> i32
// CHECK-NEXT: "func.return"(%[[SHL]]) : (i32) -> ()

// An out-of-range shl folds to 0.
// CHECK-LABEL: func.func @shl_out_of_range() -> i32 {
// CHECK-NEXT: %[[ZERO:.*]] = "gmir.g_constant"() <{"value" = 0 : i32}> : () -> i32
// CHECK-NEXT: "func.return"(%[[ZERO]]) : (i32) -> ()
