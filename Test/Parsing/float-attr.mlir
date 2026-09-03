// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
    "test.test"() { a = 1.5 : f64, b = -2.25 : f64, c = 100.5 : f64, d = 0.5 : f32, e = 1.5 : f16, f = 1.5 : bf16 } : () -> ()
    // CHECK:     "test.test"() {a = 1.5 : f64, b = -2.25 : f64, c = 100.5 : f64, d = 0.5 : f32, e = 1.5 : f16, f = 1.5 : bf16} : () -> ()
}) : () -> ()
