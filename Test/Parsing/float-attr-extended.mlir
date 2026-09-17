// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_UNREGISTERED_ROUNDTRIP

"builtin.module"() ({
    "test.test"() { a = 1.5 : f80, b = -2.25 : f80, c = 1.5 : f128, d = 0.5 : f128, e = 0x7fff8000000000000000 : f80, f = 0x1 : f128 } : () -> ()
    // CHECK:     "test.test"() {"a" = 0x3fffc000000000000000 : f80, "b" = 0xc0009000000000000000 : f80, "c" = 0x3fff8000000000000000000000000000 : f128, "d" = 0x3ffe0000000000000000000000000000 : f128, "e" = 0x7fff8000000000000000 : f80, "f" = 0x00000000000000000000000000000001 : f128} : () -> ()

    // The largest finite f80, the smallest f80 subnormal, and an f80 subnormal
    // whose mantissa has no leading one.
    "test.test"() { max = 1.189731495357231765021e+4932 : f80, min_subnormal = 3.645199531882474602528e-4951 : f80, subnormal = 1.282540566677892115121e-4937 : f80 } : () -> ()
    // CHECK:     "test.test"() {"max" = 0x7ffeffffffffffffffff : f80, "min_subnormal" = 0x00000000000000000001 : f80, "subnormal" = 0x00000000200000000000 : f80} : () -> ()
}) : () -> ()
