// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
    "test.test"() { a = 1.5 : f64, b = -2.25 : f64, c = 100.5 : f64, d = 0.5 : f32, e = 1.5 : f16, f = 1.5 : bf16 } : () -> ()
    // CHECK:     "test.test"() {"a" = 0x3ff8000000000000 : f64, "b" = 0xc002000000000000 : f64, "c" = 0x4059200000000000 : f64, "d" = 0x3f000000 : f32, "e" = 0x3e00 : f16, "f" = 0x3fc0 : bf16} : () -> ()
}) : () -> ()
