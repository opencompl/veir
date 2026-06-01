// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace

// Verify that parse errors go through ParserError.format.

"builtin.module"() ({
  ^bb0():
    %a = "builtin.module"() missing_colon
}) : () -> ()

// CHECK:invalid-syntax.mlir:7:29: error: Expected punctuation ':'
// CHECK-NEXT:     %a = "builtin.module"() missing_colon
// CHECK-NEXT:                             ^