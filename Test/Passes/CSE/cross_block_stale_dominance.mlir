// RUN: veir-opt %s -p=cse --allow-unregistered-dialect | filecheck %s

// Minimal reproducer for a stale-dominance bug in cross-block CSE.
//
// Three blocks form a straight-line chain ^A -> ^B -> ^C, each holding the
// same `add %a, %b`. All three are equivalent and ^A dominates ^B and ^C, so
// every redundant add should collapse onto the one in ^A.
//
// What actually happens: the pass computes the dominance facts once, up front,
// then CSEs ^B's add against ^A's and *erases* it. ^B sits on ^C's idom chain
// (^C -> ^B -> ^A), so erasing an op from ^B corrupts the dominance query that
// is later run -- against the *mutated* IR but the *stale* fact set -- for ^C's
// add. That query wrongly reports that ^A's add does not dominate ^C's, so the
// third add is left in place.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (i32, i32)>}> ({
  ^A(%a : i32, %b : i32):
    %1 = "llvm.add"(%a, %b) : (i32, i32) -> i32
    "llvm.br"() [^B] : () -> ()
  ^B:
    %2 = "llvm.add"(%a, %b) : (i32, i32) -> i32
    "llvm.br"() [^C] : () -> ()
  ^C:
    %3 = "llvm.add"(%a, %b) : (i32, i32) -> i32
    "llvm.return"() : () -> ()
  }) : () -> ()

  // ^A keeps the only add.
  // CHECK-LABEL: void (i32, i32)>
  // CHECK:         %[[E:.*]] = "llvm.add"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
  // CHECK-NEXT:    "llvm.br"()

  // ^B's redundant add is gone.
  // CHECK:       ^{{[0-9]+}}():
  // CHECK-NEXT:    "llvm.br"()

  // ^C's redundant add is gone too -- this is the line that fails today.
  // CHECK:       ^{{[0-9]+}}():
  // CHECK-NEXT:    "llvm.return"()
}) : () -> ()
