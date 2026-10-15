// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
^bb0(%a: i64):
  %r = "gmir.g_ptrtoint"(%a) : (i64) -> i64
}) : () -> ()

// CHECK: Error verifying input program: gmir.g_ptrtoint: Expected operand 0 to have !llvm.ptr type
