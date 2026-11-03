// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// `(A - B) - 1` equals `A + ~B` (since `-B - 1 == ~B`), so it rewrites to
// `add (xor B, -1), A`.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64) -> i64, sym_name = "foo"}> ({
  ^bb0(%a: i64, %b: i64):
    %sub = "gmir.g_sub"(%a, %b) : (i64, i64) -> i64
    %one = "gmir.g_constant"() <{value = 1 : i64}> : () -> i64
    %r = "gmir.g_sub"(%sub, %one) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: subtracting 2 (not 1) from the inner sub does not match.
  "func.func"() <{function_type = (i64, i64) -> i64, sym_name = "bar"}> ({
  ^bb0(%a: i64, %b: i64):
    %sub = "gmir.g_sub"(%a, %b) : (i64, i64) -> i64
    %two = "gmir.g_constant"() <{value = 2 : i64}> : () -> i64
    %r = "gmir.g_sub"(%sub, %two) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// Rewritten to add(xor(B, -1), A).
// CHECK:      func.func @foo(%[[A:.*]]: i64, %[[B:.*]]: i64) -> i64 {
// CHECK:      %[[M1:.*]] = "gmir.g_constant"() <{"value" = -1 : i64}> : () -> i64
// CHECK:      %[[NB:.*]] = "gmir.g_xor"(%[[B]], %[[M1]]) : (i64, i64) -> i64
// CHECK:      %[[R:.*]] = "gmir.g_add"(%[[NB]], %[[A]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[R]]) : (i64) -> ()

// Subtracting 2: `sub_one_from_sub` does not fire (it needs a 1), but `sub_to_add` rewrites
// `(A - B) - 2` into `(A - B) + (-2)`.
// CHECK:      func.func @bar(%[[NA:.*]]: i64, %[[NB2:.*]]: i64) -> i64 {
// CHECK:      %[[NSUB:.*]] = "gmir.g_sub"(%[[NA]], %[[NB2]]) : (i64, i64) -> i64
// CHECK:      %[[NC:.*]] = "gmir.g_constant"() <{"value" = -2 : i64}> : () -> i64
// CHECK:      %[[NR:.*]] = "gmir.g_add"(%[[NSUB]], %[[NC]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[NR]]) : (i64) -> ()
