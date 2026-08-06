// RUN: not veir-opt %s 2>&1 | filecheck %s

// Every element of `match.constant_types` is a type.
"builtin.module"() ({
  %a = "match.constant_types"() <{value = [i32, 4 : i32]}> : () -> !pdl.range<type>
}) : () -> ()

// CHECK: match.constant_types: expected 'value' to hold types, but got 4
