// RUN: veir-opt %s 2>&1 | filecheck %s --strict-whitespace

// Verify that parse errors go through ParserError.format.

"builtin.module"() ({
  ^bb0():
    %a = "test.op"() missing_colon
}) : () -> ()

// CHECK:Test/Parsing/invalid-syntax.mlir:7:22: error: Expected punctuation ':'
// CHECK-NEXT:     %a = "test.op"() missing_colon
// CHECK-NEXT:                      ^