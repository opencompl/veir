// RUN: veir-opt %s -p=cse --allow-unregistered-dialect | filecheck %s

// A single CSE pass already reaches a fixpoint on cross-block dependent chains,
// so wrapping the pass in a fixpoint loop adds nothing here. Eliminating the
// redundant %d1 in ^def rewrites (via RAUW) the operand of %u in ^use; because
// the pass visits definitions before uses and replaces immediately, %u is keyed
// as mul(%e, %z) by the time it is processed and merges with %u0 from the entry
// block -- all in one pass.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (i32, i32, i32)>}> ({
  ^entry(%a : i32, %b : i32, %z : i32):
    %e = "llvm.add"(%a, %b) : (i32, i32) -> i32
    %u0 = "llvm.mul"(%e, %z) : (i32, i32) -> i32
    "test.test"(%e, %u0) : (i32, i32) -> ()
    "llvm.br"() [^def] : () -> ()
  ^def:
    %d1 = "llvm.add"(%a, %b) : (i32, i32) -> i32
    "test.test"(%d1) : (i32) -> ()
    "llvm.br"() [^use] : () -> ()
  ^use:
    %u = "llvm.mul"(%d1, %z) : (i32, i32) -> i32
    "test.test"(%u) : (i32) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()

  // The entry block keeps the only add and the only mul.
  // CHECK-LABEL: void (i32, i32, i32)>
  // CHECK:         %[[E:.*]] = "llvm.add"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
  // CHECK-NEXT:    %[[U0:.*]] = "llvm.mul"(%[[E]], %{{.*}}) : (i32, i32) -> i32
  // CHECK-NEXT:    "test.test"(%[[E]], %[[U0]]) : (i32, i32) -> ()

  // ^def's redundant add is gone; it reuses %[[E]].
  // CHECK:       ^{{[0-9]+}}():
  // CHECK-NEXT:    "test.test"(%[[E]]) : (i32) -> ()

  // ^use's redundant mul is gone; it reuses %[[U0]].
  // CHECK:       ^{{[0-9]+}}():
  // CHECK-NEXT:    "test.test"(%[[U0]]) : (i32) -> ()
  // CHECK-NEXT:    "llvm.return"() : () -> ()
}) : () -> ()
