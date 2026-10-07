// RUN: VEIR_UNREGISTERED_ROUNDTRIP
// RUN: MLIR_UNREGISTERED_ROUNDTRIP
// XFAIL: *
//
// VeIR rejects opaque LLVM struct types for now.

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
    ^bb0():
      "test.opaque"() <{ty = !llvm.struct<"opaque_t", opaque>}> : () -> ()
      "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "test.opaque"() <{"ty" = !llvm.struct<"opaque_t", opaque>}> : () -> ()
