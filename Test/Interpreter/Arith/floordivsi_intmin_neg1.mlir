// RUN: veir-interpret %s | filecheck %s

// `floordivsi intMin, -1` is immediate UB (the underlying signed quotient
// overflows), matching arith.divsi.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i8}> ({
    %intmin = "arith.constant"() <{ "value" = -128 : i8 }> : () -> i8
    %negone = "arith.constant"() <{ "value" = -1 : i8 }> : () -> i8
    %r = "arith.floordivsi"(%intmin, %negone) : (i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
