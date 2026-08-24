// RUN: VEIR_UNREGISTERED_ROUNDTRIP
// The op holding the multi-block region has to be unregistered for MLIR to
// treat it as declaring a graph region, so `mlir-opt` needs the flag too and
// the MLIR_* substitutions (which pass it only to `veir-opt`) do not apply.
// RUN: %if mlir-opt %{ mlir-opt --allow-unregistered-dialect %s -o /dev/null %}

// A region holding more than one block always uses SSA dominance, whatever its
// owning operation declares: only a CFG gives the blocks an order. An
// unregistered operation declares a graph region, but this one has two blocks,
// so it is checked as an SSACFG region rather than rejected for having more
// than one block. `%v` is defined in the entry block, which dominates the
// block that uses it.

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
  ^entry:
    "unreg.wrapper"() ({
    ^bb0:
      %v = "unreg.def"() : () -> i32
      "cf.br"() [^bb1] : () -> ()
    ^bb1:
      "unreg.use"(%v) : (i32) -> ()
      "cf.br"() [^bb1] : () -> ()
    }) : () -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "func.func"() <{{.*}}> ({
// CHECK-NEXT:       ^{{.*}}():
// CHECK-NEXT:         "unreg.wrapper"() ({
// CHECK-NEXT:           ^{{.*}}():
// CHECK-NEXT:             %[[V:.*]] = "unreg.def"() : () -> i32
// CHECK-NEXT:             "cf.br"() [^[[USE:.*]]] : () -> ()
// CHECK-NEXT:           ^[[USE]]():
// CHECK-NEXT:             "unreg.use"(%[[V]]) : (i32) -> ()
// CHECK-NEXT:             "cf.br"() [^[[USE]]] : () -> ()
// CHECK-NEXT:         }) : () -> ()
// CHECK-NEXT:         "func.return"() : () -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) : () -> ()
