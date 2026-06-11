// RUN: not veir-opt %s 2>&1 | filecheck %s

// Negative test: include.from with a result. The LLZK schema forbids
// any results (it's a side-effecting declaration), and the typed
// verifier arm rejects this. If the parser routed to the unregistered
// fallthrough instead, no verifier error would fire (builtin.unregistered
// accepts any arity), so seeing this exact message confirms the typed
// `.include Include_.from` path is reached.

// CHECK: Error verifying input program: Expected 0 results
"builtin.module"() ({
  %0 = "include.from"() <{sym_name = "lib_a", path = "lib_a.llzk"}> : () -> (i32)
}) : () -> ()
