// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// `y +w sext_inreg(c, 1)` for a 0-or-1 `g_icmp` `c` becomes `y -w c`: the `sext_inreg` becomes
// `0 - c`, which the word addition absorbs.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64, i64) -> i64, sym_name = "foo"}> ({
  ^bb0(%a: i64, %b: i64, %y: i64):
    %c = "gmir.g_icmp"(%a, %b) <{"predicate" = 1 : i64}> : (i64, i64) -> i64
    %s = "gmir.g_sext_inreg"(%c) <{"sz" = 1 : i64}> : (i64) -> i64
    %r = "gmir.g_addw"(%y, %s) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      func.func @foo(%{{.*}}: i64, %{{.*}}: i64, %[[Y:.*]]: i64) -> i64 {
// CHECK:      %[[C:.*]] = "gmir.g_icmp"
// CHECK-NEXT: %[[R:.*]] = "gmir.g_subw"(%[[Y]], %[[C]])
// CHECK-NEXT: "func.return"(%[[R]])
