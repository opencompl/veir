// RUN: not veir-opt %s 2>&1 | filecheck %s

// A result width that is not a whole number of copies is rejected by the verifier. Seven bits
// cannot hold a whole number of three-bit copies, and `Data.Comb.replicate` fills two copies and
// leaves the seventh bit zero, so an unchecked width answers with a repetition cut short rather
// than failing.

"builtin.module"() ({
^bb0(%a: i3):
  %r = "comb.replicate"(%a) : (i3) -> i7
}) : () -> ()

// CHECK: comb.replicate: an i7 result is not a whole number of i3 copies
