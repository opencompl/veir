// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_UNREGISTERED_ROUNDTRIP

"builtin.module"() ({
    "test.test"() <{test = 23 : i32, "fo/no" = 1 : i32}> : () -> ()
    // CHECK:     "test.test"() : () -> ()
}) : () -> ()
