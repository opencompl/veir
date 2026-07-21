// RUN: veir-opt %s -p=cse --allow-unregistered-dialect | filecheck %s

"builtin.module"() ({
  // The pass processes the outer block before the nested region. A candidate
  // that appears after the region-owning op in the outer block must not be used
  // inside that nested region, because it does not dominate the nested op.
  "llvm.func"() <{function_type = !llvm.func<void (i32, i32)>, sym_name = "region_order"}> ({
  ^entry(%a : i32, %b : i32):
    "test.region"() ({
    ^inner:
      %inner = "llvm.add"(%a, %b) : (i32, i32) -> i32
      "test.test"(%inner) : (i32) -> ()
    }) : () -> ()
    %late = "llvm.add"(%a, %b) : (i32, i32) -> i32
    "test.test"(%late) : (i32) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()

  // CHECK-LABEL: void (i32, i32)>
  // CHECK:       "test.region"() ({
  // CHECK-NEXT:  ^{{[0-9]+}}():
  // CHECK-NEXT:    %[[INNER:.*]] = "llvm.add"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
  // CHECK-NEXT:    "test.test"(%[[INNER]]) : (i32) -> ()
  // CHECK-NEXT:  }) : () -> ()
  // CHECK-NEXT:  %[[LATE:.*]] = "llvm.add"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
  // CHECK-NEXT:  "test.test"(%[[LATE]]) : (i32) -> ()
}) : () -> ()
