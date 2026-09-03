// RUN: not veir-opt %s -p=cir-to-std 2>&1 | filecheck %s

// A bitcast (kind 1) round-trips but has no lowering.
// CHECK: Error while applying cir-to-std lowering
"builtin.module"() ({
  "cir.func"() <{function_type = !cir.func<(!cir.int<s, 32>) -> !cir.int<u, 32>>, sym_name = "f"}> ({
  ^bb0(%a : !cir.int<s, 32>):
    %p = "cir.cast"(%a) <{kind = 1 : i32}> : (!cir.int<s, 32>) -> !cir.int<u, 32>
    "cir.return"(%p) : (!cir.int<u, 32>) -> ()
  }) : () -> ()
}) : () -> ()
