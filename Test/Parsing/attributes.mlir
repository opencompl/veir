// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
    // CHECK:     "test.test"() {"fo/no" = 1 : i32, "location" = loc("source":10:20), "nested" = @root::@child::@leaf, "test" = 23 : i32} : () -> ()
    "test.test"() { test = 23 : i32, "fo/no" = 1 : i32, "location" = loc("source":10:20), "nested" = @root::@child::@leaf } : () -> ()
}) : () -> ()
