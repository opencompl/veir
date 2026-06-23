// RUN: veir-opt %s -p=canonicalize | filecheck %s

// A commutative op with more than one result (`arith.mului_extended`
// produces the low word and the high/overflow word): the constant is
// still pushed to the right and all results are preserved.
"builtin.module"() ({
  "func.func"() <{function_type = (i32) -> i32, sym_name = "main"}> ({
    ^bb0(%x : i32):
      // CHECK:      ^{{.*}}(%[[X:.*]] : i32):
      %c = "arith.constant"() <{ "value" = 5 : i32 }> : () -> i32
      // CHECK-NEXT: %[[C:.*]] = "arith.constant"() <{"value" = 5 : i32}> : () -> i32
      %lo, %hi = "arith.mului_extended"(%c, %x) : (i32, i32) -> (i32, i32)
      // CHECK-NEXT: %[[R:.*]]:2 = "arith.mului_extended"(%[[X]], %[[C]]) : (i32, i32) -> (i32, i32)
      "func.return"(%lo) : (i32) -> ()
      // CHECK-NEXT: "func.return"(%[[R]]#0) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
