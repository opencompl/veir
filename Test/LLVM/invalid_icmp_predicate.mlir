// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() ({
    ^bb0(%a: i64, %b: i64):
      %r = "llvm.icmp"(%a, %b) <{"predicate" = 11 : i64}> : (i64, i64) -> i1
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.icmp: invalid predicate 11
