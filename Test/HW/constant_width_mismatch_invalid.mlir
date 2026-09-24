// RUN: not veir-opt %s 2>&1 | filecheck %s

// As in CIRCT, the attribute's width must match the result type.

"builtin.module"() ({
  "hw.module"() <{module_type = !hw.modty<output out : i8>, parameters = [], per_port_attrs = [], sym_name = "m"}> ({
    %c = "hw.constant"() <{value = 3 : i4}> : () -> i8
    "hw.output"(%c) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: hw.constant: attribute bitwidth 4 doesn't match return type
