// RUN: veir-opt %s -p=coerce-mod-arith-function-boundaries,reconcile-cast | filecheck %s

"builtin.module"() ({

  // `mod_arith` function boundaries can be coerced to their storage integer type.
  // The pre-existing `i32 <-> !mod_arith.int<7 : i32>` boundary casts then form
  // identity round trips and are reconciled away, so the `arith.addi` consumes the
  // function arguments directly and the function returns the `arith.addi` result.
    "func.func"() <{sym_name = "arith_add", function_type = (!mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>) -> !mod_arith.int<7 : i32>}> ({
    ^bb(%a: !mod_arith.int<7 : i32>, %b: !mod_arith.int<7 : i32>):
      %ai = "builtin.unrealized_conversion_cast"(%a) : (!mod_arith.int<7 : i32>) -> i32
      %bi = "builtin.unrealized_conversion_cast"(%b) : (!mod_arith.int<7 : i32>) -> i32
      %sum = "arith.addi"(%ai, %bi) : (i32, i32) -> i32
      %out = "builtin.unrealized_conversion_cast"(%sum) : (i32) -> !mod_arith.int<7 : i32>
      "func.return"(%out) : (!mod_arith.int<7 : i32>) -> ()
      // CHECK:      "func.func"() <{"function_type" = (i32, i32) -> i32, "sym_name" = "arith_add"}>
      // CHECK-NEXT: ^{{.*}}([[A:%.*]] : i32, [[B:%.*]] : i32):
      // CHECK-NEXT:   [[SUM:%.*]] = "arith.addi"([[A]], [[B]]) : (i32, i32) -> i32
      // CHECK-NEXT:   "func.return"([[SUM]]) : (i32) -> ()
    }) : () -> ()

}) : () -> ()
