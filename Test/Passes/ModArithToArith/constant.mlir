// RUN: veir-opt %s -p=mod-arith-to-arith | filecheck %s

// Lowering of mod_arith.constant: the value is assumed to already be in [0, q)
// and materialised as an arith.constant cast up to the mod_arith type.

"builtin.module"() ({
  "func.func"() <{function_type = () -> !mod_arith.int<17 : i32>, sym_name = "main"}> ({
    ^bb0():
      %c = "mod_arith.constant"() <{"value" = 3 : i32}> : () -> !mod_arith.int<17 : i32>
      "func.return"(%c) : (!mod_arith.int<17 : i32>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "func.func"
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:   [[C:%.*]] = "arith.constant"() <{"value" = 3 : i32}> : () -> i32
// CHECK-NEXT:   [[RES:%.*]] = "builtin.unrealized_conversion_cast"([[C]]) : (i32) -> !mod_arith.int<17 : i32>
// CHECK-NEXT:   "func.return"([[RES]]) : (!mod_arith.int<17 : i32>) -> ()
