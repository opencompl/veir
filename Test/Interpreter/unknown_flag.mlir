// RUN: not veir-interpret --unknown %s 2>&1 | filecheck %s

"builtin.module"() ({
}) : () -> ()

// CHECK:      Unrecognized flag '--unknown'.
// CHECK-NEXT: Usage: veir-interpret [--ctree] [filename]
