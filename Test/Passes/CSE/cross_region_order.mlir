// RUN: veir-opt %s -p=cse | filecheck %s

"builtin.module"() ({
  // Negative: the pass processes the outer block before the nested region. A
  // candidate that appears after the region-owning op in the outer block must
  // not be used inside that nested region, because it does not dominate the
  // nested op.
  "llvm.func"() <{function_type = !llvm.func<void (i32, i32)>, sym_name = "region_order"}> ({
  ^entry(%a : i32, %b : i32):
    "test.test"() ({
    ^inner:
      %inner = "llvm.add"(%a, %b) : (i32, i32) -> i32
      "test.test"(%inner) : (i32) -> ()
    }) : () -> ()
    %late = "llvm.add"(%a, %b) : (i32, i32) -> i32
    "test.test"(%late) : (i32) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()

  // CHECK-LABEL: "sym_name" = "region_order"
  // CHECK:       "test.test"() ({
  // CHECK-NEXT:  ^{{[0-9]+}}():
  // CHECK-NEXT:    %[[INNER:.*]] = "llvm.add"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
  // CHECK-NEXT:    "test.test"(%[[INNER]]) : (i32) -> ()
  // CHECK-NEXT:  }) : () -> ()
  // CHECK-NEXT:  %[[LATE:.*]] = "llvm.add"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
  // CHECK-NEXT:  "test.test"(%[[LATE]]) : (i32) -> ()

  // Positive: a definition that precedes the region-owning op *does* dominate
  // the nested op, so the nested recomputation is eliminated and rewired to it.
  // Without this case the negative test above would pass vacuously if nested
  // regions were never traversed at all.
  "llvm.func"() <{function_type = !llvm.func<void (i32, i32)>, sym_name = "region_reuse"}> ({
  ^entry(%c : i32, %d : i32):
    %early = "llvm.add"(%c, %d) : (i32, i32) -> i32
    "test.test"(%early) : (i32) -> ()
    "test.test"() ({
    ^inner:
      %dup = "llvm.add"(%c, %d) : (i32, i32) -> i32
      "test.test"(%dup) : (i32) -> ()
    }) : () -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()

  // CHECK-LABEL: "sym_name" = "region_reuse"
  // CHECK:         %[[EARLY:.*]] = "llvm.add"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
  // CHECK-NEXT:    "test.test"(%[[EARLY]]) : (i32) -> ()
  // CHECK-NEXT:    "test.test"() ({
  // CHECK-NEXT:  ^{{[0-9]+}}():
  // The nested add is gone; it reuses the definition from outside the region.
  // CHECK-NEXT:    "test.test"(%[[EARLY]]) : (i32) -> ()
  // CHECK-NEXT:  }) : () -> ()
  // CHECK-NEXT:  "llvm.return"() : () -> ()
}) : () -> ()
