// RUN: not veir-opt %s -p=cir-to-std 2>&1 | filecheck %s

// Saturating arithmetic has no arith counterpart.
// CHECK: Error while applying cir-to-std lowering

"builtin.module"() ({
  "cir.func"() <{function_type = !cir.func<(!cir.int<s, 32>) -> !cir.int<s, 32>>, sym_name = "f"}> ({
  ^bb0(%a : !cir.int<s, 32>):
    %s = "cir.add"(%a, %a) <{no_signed_wrap = false, no_unsigned_wrap = false, saturated}> : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
    "cir.return"(%s) : (!cir.int<s, 32>) -> ()
  }) : () -> ()
}) : () -> ()
