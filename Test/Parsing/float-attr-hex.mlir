// RUN: VEIR_ROUNDTRIP

// Verify that a 0x-prefixed hexadecimal literal is parsed as the raw IEEE-754
// bit pattern of the type and round-trips. The printer emits the bit pattern,
// zero-padded to the type's width (so `0x1 : f32` prints as `0x00000001 : f32`).
// Includes special values: +inf, -inf, NaN, -0.0, +0.0.

"builtin.module"() ({
    "test.test"() { a = 0x7f800000 : f32, b = 0xff80000000000000 : f64, c = 0x7fc00000 : f32, d = 0x8000 : f16, e = 0x00000000 : f32, f = 0x1 : f32 } : () -> ()
    // CHECK:     "test.test"() {"a" = 0x7f800000 : f32, "b" = 0xff80000000000000 : f64, "c" = 0x7fc00000 : f32, "d" = 0x8000 : f16, "e" = 0x00000000 : f32, "f" = 0x00000001 : f32} : () -> ()
}) : () -> ()
