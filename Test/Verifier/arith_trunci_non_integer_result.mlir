// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = () -> f64, sym_name = "main"}> ({
    %x = "arith.constant"() <{ "value" = 3 : i16 }> : () -> i16
    %trunc = "arith.trunci"(%x) : (i16) -> f64
    "func.return"(%trunc) : (f64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: arith.trunci: Expected integer result type
