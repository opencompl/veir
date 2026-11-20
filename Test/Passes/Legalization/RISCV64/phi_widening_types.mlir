// RUN: veir-opt --split-input-file %s > /dev/null
// RUN: not veir-opt --split-input-file %s -p=legalize-riscv64 2>&1 | filecheck %s

// Each input verifies. Widening requires the source type of g_anyext and
// the result type of g_trunc to be signless integers of positive width.

// CHECK: unable to widen a block argument: expected a narrower signless integer of positive width
"builtin.module"() ({
  "func.func"() <{sym_name = "signed", function_type = (si8) -> si8}> ({
  ^entry(%x : si8):
    "cf.br"(%x) [^next] : (si8) -> ()
  ^next(%a : si8):
    "func.return"(%a) : (si8) -> ()
  }) : () -> ()
}) : () -> ()

// -----

// CHECK: unable to widen a block argument: expected a narrower signless integer of positive width
"builtin.module"() ({
  "func.func"() <{sym_name = "unsigned", function_type = (ui8) -> ui8}> ({
  ^entry(%x : ui8):
    "cf.br"(%x) [^next] : (ui8) -> ()
  ^next(%a : ui8):
    "func.return"(%a) : (ui8) -> ()
  }) : () -> ()
}) : () -> ()

// -----

// CHECK: unable to widen a block argument: expected a narrower signless integer of positive width
"builtin.module"() ({
  "func.func"() <{sym_name = "zero_width", function_type = (i0) -> i0}> ({
  ^entry(%x : i0):
    "cf.br"(%x) [^next] : (i0) -> ()
  ^next(%a : i0):
    "func.return"(%a) : (i0) -> ()
  }) : () -> ()
}) : () -> ()

// -----

// The i32 phi widens even when the same block has a legal-width signed phi.
// CHECK: ^{{.*}}(%{{.*}} : i64, %{{.*}} : si64):
"builtin.module"() ({
  "func.func"() <{sym_name = "mixed", function_type = (i32, si64) -> si64}> ({
  ^entry(%x : i32, %y : si64):
    "cf.br"(%x, %y) [^next] : (i32, si64) -> ()
  ^next(%a : i32, %b : si64):
    "func.return"(%b) : (si64) -> ()
  }) : () -> ()
}) : () -> ()

// -----

// The default and both cases forward separate values to the same block argument.
// CHECK-LABEL: func.func @repeated_switch_destination
// CHECK-SAME: (%[[KEY:.*]]: i32, %[[D:.*]]: i32, %[[A:.*]]: i32, %[[B:.*]]: i32)
// CHECK-DAG: %[[WD:.*]] = "gmir.g_anyext"(%[[D]]) : (i32) -> i64
// CHECK-DAG: %[[WA:.*]] = "gmir.g_anyext"(%[[A]]) : (i32) -> i64
// CHECK-DAG: %[[WB:.*]] = "gmir.g_anyext"(%[[B]]) : (i32) -> i64
// CHECK: "llvm.switch"(%[[KEY]], %[[WD]], %[[WA]], %[[WB]]){{.*}} : (i32, i64, i64, i64) -> ()
// CHECK: ^{{.*}}(%{{.*}} : i64):
"builtin.module"() ({
  "func.func"() <{sym_name = "repeated_switch_destination", function_type = (i32, i32, i32, i32) -> i32}> ({
  ^entry(%key : i32, %d : i32, %a : i32, %b : i32):
    "llvm.switch"(%key, %d, %a, %b) [^join, ^join, ^join]
      <{case_operand_segments = array<i32: 1, 1>, case_values = dense<[13, 35]> : vector<2xi32>,
        operandSegmentSizes = array<i32: 1, 1, 2>}> : (i32, i32, i32, i32) -> ()
  ^join(%v : i32):
    "func.return"(%v) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
