// RUN: VEIR_UNREGISTERED_ROUNDTRIP
// RUN: MLIR_UNREGISTERED_ROUNDTRIP

"builtin.module"() ({
  "test.op"() <{attr = 42 : si32}> : () -> ()
  "test.op"() <{attr = 7 : ui16}> : () -> ()
  "test.op"() <{attr = 1 : i8}> : () -> ()
  "test.op"() <{attr = 0 : si1}> : () -> ()
  "test.op"() <{attr = 255 : ui8}> : () -> ()
}) : () -> ()

// CHECK: 42 : si32
// CHECK: 7 : ui16
// CHECK: 1 : i8
// CHECK: 0 : si1
// CHECK: 255 : ui8
