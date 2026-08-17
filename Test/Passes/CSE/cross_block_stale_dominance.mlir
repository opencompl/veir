// RUN: veir-opt %s -p=cse --allow-unregistered-dialect | filecheck %s

// Regression test for stale dominance facts in cross-block CSE.
//
// Three blocks form a straight-line chain ^A -> ^B -> ^C, each holding the
// same `add %a, %b`. All three are equivalent and ^A dominates ^B and ^C, so
// every redundant add should collapse onto the one in ^A.
//
// Dominator facts are anchored directly to blocks so erasing ^B's first
// operation does not prevent the later query from recognizing that ^A
// dominates ^C.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (i32, i32)>, sym_name = "stale_dominance"}> ({
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

  // ^C's redundant add is gone too.
  // CHECK:       ^{{[0-9]+}}():
  // CHECK-NEXT:    "llvm.return"()
}) : () -> ()
