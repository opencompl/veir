// RUN: veir-opt %s | filecheck %s
"builtin.module"() ({
^bb0(%arg0: !cuda_tile.ptr<i1>):
    %0 = "test.test"() : () -> !cuda_tile.ptr<i1>
}) : () -> ()

// CHECK-NEXT: "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}(%{{.*}} : !cuda_tile.ptr<i1>):
// CHECK-NEXT:     %{{.*}} = "test.test"() : () -> !cuda_tile.ptr<i1>
// CHECK-NEXT: }) : () -> ()
