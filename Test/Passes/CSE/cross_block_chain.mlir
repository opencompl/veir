// RUN: veir-opt %s -p=cse --allow-unregistered-dialect | filecheck %s
// XFAIL: *
//
// Eliminating the redundant %d1 in ^def rewrites (via RAUW) the operand of %u in
// ^use, so %u becomes mul(%e, %z) and should merge with %u0 from the entry block.
// It does not: the same stale-dominance bug as cross_block_stale_dominance bites
// here -- erasing %d1 from ^def stales the dominance query later run for ^use, so
// the mul in ^use is left in place. A second CSE pass (fresh facts) clears it.
// We are not fixing this now.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (i32, i32, i32)>, sym_name = "chain"}> ({
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
