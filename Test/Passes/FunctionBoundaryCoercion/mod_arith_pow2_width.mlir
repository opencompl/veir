// RUN: veir-opt %s -p=coerce-mod-arith-function-boundaries-pow2-width,reconcile-cast | filecheck %s

"builtin.module"() ({

  // With the pow2-width variant, `mod_arith` boundaries with a non-power-of-two storage
  // type (i33) are coerced to the power-of-two-widened storage type (i64) — the same
  // representation type the `mod-arith-to-arith-pow2-width` lowering uses. The boundary
  // casts below (as that lowering would emit them) then form identity round trips and
  // are reconciled away.
    "func.func"() <{sym_name = "arith_add", function_type = (!mod_arith.int<7 : i33>, !mod_arith.int<7 : i33>) -> !mod_arith.int<7 : i33>}> ({
    ^bb(%a: !mod_arith.int<7 : i33>, %b: !mod_arith.int<7 : i33>):
      %ai = "builtin.unrealized_conversion_cast"(%a) : (!mod_arith.int<7 : i33>) -> i64
      %bi = "builtin.unrealized_conversion_cast"(%b) : (!mod_arith.int<7 : i33>) -> i64
      %sum = "arith.addi"(%ai, %bi) : (i64, i64) -> i64
      %out = "builtin.unrealized_conversion_cast"(%sum) : (i64) -> !mod_arith.int<7 : i33>
      "func.return"(%out) : (!mod_arith.int<7 : i33>) -> ()
      // CHECK:      "func.func"() <{"function_type" = (i64, i64) -> i64, "sym_name" = "arith_add"}>
      // CHECK-NEXT: ^{{.*}}([[A:%.*]] : i64, [[B:%.*]] : i64):
      // CHECK-NEXT:   [[SUM:%.*]] = "arith.addi"([[A]], [[B]]) : (i64, i64) -> i64
      // CHECK-NEXT:   "func.return"([[SUM]]) : (i64) -> ()
    }) : () -> ()

}) : () -> ()
