// RUN: VEIR_ROUNDTRIP

// A decimal literal that overflows the type must round to a signed infinity, not
// to a NaN.  These values sit in the binade immediately above the largest finite
// value, where the biased exponent lands on the reserved all-ones pattern.

"builtin.module"() ({
    "test.test"() { a = 3.5e38 : f32, b = -3.5e38 : f32, c = 2.0e308 : f64, d = 70000.0 : f16, e = 4.0e38 : bf16, f = 1.0e5 : f8E5M2 } : () -> ()
    // CHECK:     "test.test"() {"a" = 0x7f800000 : f32, "b" = 0xff800000 : f32, "c" = 0x7ff0000000000000 : f64, "d" = 0x7c00 : f16, "e" = 0x7f80 : bf16, "f" = 0x7c : f8E5M2} : () -> ()
}) : () -> ()