// RUN: veir-opt %s | filecheck %s

"builtin.module"() ({
    "unregistered.op"() : () -> ()
    %1 = "unregistered.op"() : () -> !foo.bar
    %2 = "unregistered.op"() : () -> !foo.bar<baz>
    // CHECK:     "builtin.unregistered"() : () -> ()
    // CHECK-NEXT: %{{.*}} = "builtin.unregistered"() : () -> !foo.bar
    // CHECK-NEXT: %{{.*}} = "builtin.unregistered"() : () -> !foo.bar<baz>
}) : () -> ()
