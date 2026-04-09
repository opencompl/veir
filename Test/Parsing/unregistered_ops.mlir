// RUN: veir-opt %s | filecheck %s

"builtin.module"() ({
    "unregistered.op"() : () -> ()
    // CHECK:     "builtin.unregistered"() : () -> ()
}) : () -> ()
