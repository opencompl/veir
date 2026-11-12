// RUN: veir-opt %s -p=llvm-to-gmir,prelegalizer-combiner-riscv64 | filecheck %s

// XFAIL: *
// Needs `dropAssume`, commented out of the pass as unproven.

// `llvm.intr.assume` only adds UB, so the pre-legalizer combiner drops it.
"builtin.module"() ({
  "func.func"() <{function_type = (i1) -> (), sym_name = "assume"}> ({
  ^bb0(%c: i1):
    "llvm.intr.assume"(%c) <{op_bundle_sizes = array<i32>}> : (i1) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: func.func @assume
// CHECK-NOT:   llvm.intr.assume
// CHECK:       "func.return"() : () -> ()
