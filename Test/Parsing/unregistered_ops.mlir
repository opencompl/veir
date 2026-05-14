// RUN: veir-opt %s | filecheck %s

"builtin.module"() ({
    "unregistered.op_one"() : () -> ()
    %1 = "unregistered.op_two"() : () -> !foo.bar
    %2 = "unregistered.op_three"() : () -> !foo.bar<baz>
    "unregistered.op_four"() <{foo = 1 : i32}> : () -> ()
    // CHECK:      "unregistered.op_one"() : () -> ()
    // CHECK-NEXT: %{{.*}} = "unregistered.op_two"() : () -> !foo.bar
    // CHECK-NEXT: %{{.*}} = "unregistered.op_three"() : () -> !foo.bar<baz>
    // CHECK-NEXT: "unregistered.op_four"() <{"foo" = 1 : i32}> : () -> ()
}) : () -> ()
