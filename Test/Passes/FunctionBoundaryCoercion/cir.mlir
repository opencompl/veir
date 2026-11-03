// RUN: veir-opt %s -p=coerce-cir-function-boundaries,reconcile-cast | filecheck %s

"builtin.module"() ({

  // `cir` function boundaries are coerced to the builtin integer of the same width.
  // The pre-existing `!cir.int <-> iN` and `!cir.bool <-> i1` boundary casts then form
  // identity round trips and are reconciled away, so the `arith` ops consume the function
  // arguments directly and the function returns the `arith.cmpi` result.
  "cir.func"() <{sym_name = "arith_lt", function_type = !cir.func<(!cir.int<s, 32>, !cir.int<u, 8>) -> !cir.bool>}> ({
  ^bb(%a : !cir.int<s, 32>, %b : !cir.int<u, 8>):
    %ai = "builtin.unrealized_conversion_cast"(%a) : (!cir.int<s, 32>) -> i32
    %bi = "builtin.unrealized_conversion_cast"(%b) : (!cir.int<u, 8>) -> i8
    %bw = "arith.extui"(%bi) : (i8) -> i32
    %lt = "arith.cmpi"(%ai, %bw) <{predicate = 2 : i64}> : (i32, i32) -> i1
    %out = "builtin.unrealized_conversion_cast"(%lt) : (i1) -> !cir.bool
    "cir.return"(%out) : (!cir.bool) -> ()
    // CHECK:      "cir.func"() <{"function_type" = !cir.func<(i32, i8) -> i1>, "sym_name" = "arith_lt"}>
    // CHECK-NEXT: ^{{.*}}([[A:%.*]] : i32, [[B:%.*]] : i8):
    // CHECK-NEXT:   [[BW:%.*]] = "arith.extui"([[B]]) : (i8) -> i32
    // CHECK-NEXT:   [[LT:%.*]] = "arith.cmpi"([[A]], [[BW]]) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
    // CHECK-NEXT:   "cir.return"([[LT]]) : (i1) -> ()
  }) : () -> ()

}) : () -> ()
