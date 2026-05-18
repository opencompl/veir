// RUN: veir-opt %s 2>&1 | filecheck %s

// Verify that parse errors go through ParserError.format.
// Position are not yet passed to `ParserError` everywhere, so it uses an unknown location here.

"builtin.module"() ({
  ^bb0():
    %a = "test.op"() missing_colon
}) : () -> ()

// CHECK: <unknown location>: error: Expected punctuation ':'
