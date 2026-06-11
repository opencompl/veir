// RUN: not veir-opt %s 2>&1 | filecheck %s

// Negative test: global.read with no name_ref should fail in the typed
// IncludeFromProperties-style dispatch — Properties.fromAttrDict for
// global.read throws "missing 'name_ref' property". The unregistered
// fallthrough would accept; this asserts the typed dispatch is reached.

// CHECK: missing 'name_ref' property
"builtin.module"() ({
  %0 = "global.read"() : () -> i32
}) : () -> ()
