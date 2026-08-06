// RUN: veir-opt %s -p=mod-arith-pow2-width | filecheck %s

// The `mod-arith-pow2-width` pass group lowers `mod_arith` all the way to `arith` like
// `mod-arith`, but rounds every integer width the lowering chooses up to a power of two.
// The property under test: starting from a non-power-of-two storage type (i29), no
// non-power-of-two integer type and no `unrealized_conversion_cast` survives the pipeline.

"builtin.module"() ({
  "func.func"() <{function_type = (!mod_arith.int<12289 : i29>, !mod_arith.int<12289 : i29>) -> !mod_arith.int<12289 : i29>, sym_name = "chain"}> ({
  ^bb0(%a : !mod_arith.int<12289 : i29>, %b : !mod_arith.int<12289 : i29>):
    %c5 = "mod_arith.constant"() <{"value" = 5 : i29}> : () -> !mod_arith.int<12289 : i29>
    %s = "mod_arith.add"(%a, %b) : (!mod_arith.int<12289 : i29>, !mod_arith.int<12289 : i29>) -> !mod_arith.int<12289 : i29>
    %d = "mod_arith.sub"(%a, %b) : (!mod_arith.int<12289 : i29>, !mod_arith.int<12289 : i29>) -> !mod_arith.int<12289 : i29>
    %m = "mod_arith.mul"(%s, %d) : (!mod_arith.int<12289 : i29>, !mod_arith.int<12289 : i29>) -> !mod_arith.int<12289 : i29>
    %r = "mod_arith.mul"(%m, %c5) : (!mod_arith.int<12289 : i29>, !mod_arith.int<12289 : i29>) -> !mod_arith.int<12289 : i29>
    %out = "mod_arith.add"(%r, %a) : (!mod_arith.int<12289 : i29>, !mod_arith.int<12289 : i29>) -> !mod_arith.int<12289 : i29>
    "func.return"(%out) : (!mod_arith.int<12289 : i29>) -> ()
  }) : () -> ()
}) : () -> ()

// The boundary is coerced to the power-of-two-widened storage type (i29 -> i32) ...
// CHECK: "func.func"() <{"function_type" = (i32, i32) -> i32, "sym_name" = "chain"}> ({

// ... and from here to the end of the output, nothing mod_arith-ish, no cast,
// and no non-power-of-two width survives.
// CHECK-NOT: mod_arith
// CHECK-NOT: unrealized_conversion_cast
// CHECK-NOT: i29
// CHECK-NOT: i30
// CHECK-NOT: i58
// CHECK-NOT: i87
