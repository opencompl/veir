// RUN: VEIR_UNREGISTERED_ROUNDTRIP
// RUN: MLIR_UNREGISTERED_ROUNDTRIP

"builtin.module"() ({
  "test.op"() {flat = @a, sym = @a::@b::@c} : () -> ()
}) : () -> ()

// CHECK: "test.op"() {"flat" = @a, "sym" = @a::@b::@c} : () -> ()
