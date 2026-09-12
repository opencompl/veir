// RUN: veir-opt %s -p=canonicalize | filecheck %s --check-prefix=ONCE
// RUN: veir-opt %s -p=canonicalize,canonicalize | filecheck %s --check-prefix=TWICE
// RUN: veir-opt %s -p='canonicalize{fold=false},canonicalize' | filecheck %s --check-prefix=ONCE

// A disabled first pass must not propagate the zero early: otherwise the next
// pass would already fold the exposed identity instead of producing ONCE's IR.

"builtin.module"() ({
  // The propagated zero exposes an identity, which deliberately waits until
  // the next pass invocation. Local folding alone cannot resolve the argument.
  "func.func"() <{function_type = (i32) -> i32, sym_name = "identity"}> ({
  ^entry(%x : i32):
    %zero = "arith.constant"() <{value = 0 : i32}> : () -> i32
    "cf.br"(%zero) [^exit] : (i32) -> ()
  ^exit(%forwarded : i32):
    %result = "arith.addi"(%x, %forwarded) : (i32, i32) -> i32
    "func.return"(%result) : (i32) -> ()
  }) : () -> ()
  // ONCE-LABEL: func.func @identity
  // ONCE-SAME: (%[[X:.*]]: i32)
  // ONCE: "cf.br"
  // ONCE-NEXT: ^{{.*}}(%{{.*}}: i32):
  // ONCE-NEXT: %[[ZERO:.*]] = "arith.constant"() <{"value" = 0 : i32}>
  // ONCE-NEXT: %[[RESULT:.*]] = "arith.addi"(%[[X]], %[[ZERO]])
  // ONCE-NEXT: "func.return"(%[[RESULT]])
  // TWICE-LABEL: func.func @identity
  // TWICE-SAME: (%[[X:.*]]: i32)
  // TWICE: "cf.br"
  // TWICE-NEXT: ^{{.*}}(%{{.*}}: i32):
  // TWICE-NEXT: "func.return"(%[[X]])

  // Propagation can replace just one result. The sum remains unknown, so the
  // extended add must survive even though its overflow result is replaced.
  "func.func"() <{function_type = (i32) -> (i32, i1), sym_name = "partial_result"}> ({
  ^entry(%x : i32):
    %zero = "arith.constant"() <{value = 0 : i32}> : () -> i32
    "cf.br"(%zero) [^exit] : (i32) -> ()
  ^exit(%forwarded : i32):
    %sum, %overflow = "arith.addui_extended"(%x, %forwarded) : (i32, i32) -> (i32, i1)
    "func.return"(%sum, %overflow) : (i32, i1) -> ()
  }) : () -> ()
  // ONCE-LABEL: func.func @partial_result
  // ONCE-SAME: (%[[X:.*]]: i32)
  // ONCE: "cf.br"
  // ONCE-NEXT: ^{{.*}}(%{{.*}}: i32):
  // ONCE-NEXT: %[[ZERO:.*]] = "arith.constant"() <{"value" = 0 : i32}>
  // ONCE-NEXT: %[[FALSE:.*]] = "arith.constant"() <{"value" = 0 : i1}>
  // ONCE-NEXT: %[[SUM:.*]]:2 = "arith.addui_extended"(%[[X]], %[[ZERO]])
  // ONCE-NEXT: "func.return"(%[[SUM]]#0, %[[FALSE]])
  // TWICE-LABEL: func.func @partial_result
  // TWICE-SAME: (%[[X:.*]]: i32)
  // TWICE: "cf.br"
  // TWICE-NEXT: ^{{.*}}(%{{.*}}: i32):
  // TWICE-NEXT: %[[FALSE:.*]] = "arith.constant"() <{"value" = 0 : i1}>
  // TWICE-NEXT: "func.return"(%[[X]], %[[FALSE]])
}) : () -> ()
