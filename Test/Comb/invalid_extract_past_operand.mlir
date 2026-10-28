// RUN: not veir-opt %s 2>&1 | filecheck %s

// An out-of-range extraction window is rejected by the verifier. Extracting four bits at offset
// 6 reads bits 6..9 of an i8, and `Data.Comb.extract` reads the bits above the operand as zero,
// so an unchecked window answers 0b0010 rather than failing -- a plausible value, and the reason
// the bound belongs in the verifier.

"builtin.module"() ({
^bb0(%a: i8):
  %r = "comb.extract"(%a) <{"lowBit" = 6 : i64}> : (i8) -> i4
}) : () -> ()

// CHECK: comb.extract: extracting i4 at offset 6 reads past an i8 operand
