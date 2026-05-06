// RUN: veir-opt %s | filecheck %s

"builtin.module"() ({
    "test.test"() { test = 23 : i32, "fo/no" = 1 : i32, "location" = loc("source":10:20) } : () -> ()
    // CHECK:     "test.test"() {"fo/no" = 1 : i32, "location" = loc("source":10:20), "test" = 23 : i32} : () -> ()
}) : () -> ()
