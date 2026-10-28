// RUN: not veir-opt %s 2>&1 | filecheck %s

// A negative offset is rejected by the verifier rather than clamped. `Int.toNat` would send -2
// to 0, naming a window the operation never asked for, and would extract from that window
// without complaint.

"builtin.module"() ({
^bb0(%a: i8):
  %r = "comb.extract"(%a) <{"lowBit" = -2 : i64}> : (i8) -> i4
}) : () -> ()

// CHECK: comb.extract: 'lowBit' cannot be negative, but got -2
