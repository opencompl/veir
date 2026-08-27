// RUN: veir-opt %s | filecheck %s

// Exercise each branch in the custom func.func printer. The input uses generic
// syntax so that the CHECK lines cover the custom syntax printed by veir-opt.
"builtin.module"() ({
  // Defined function with entry-block arguments and one result.
  "func.func"() <{function_type = (i32) -> i32, sym_name = "identity"}> ({
  ^bb0(%arg0: i32):
    "func.return"(%arg0) : (i32) -> ()
  }) : () -> ()

  // Visibility and an extra function attribute.
  "func.func"() <{function_type = (i64) -> i64, sym_name = "private_fn", sym_visibility = "private", extra = 7 : i64}> ({
  ^bb0(%arg0: i64):
    "func.return"(%arg0) : (i64) -> ()
  }) : () -> ()

  // A non-default visibility.
  "func.func"() <{function_type = () -> (), sym_name = "nested_fn", sym_visibility = "nested"}> ({
  ^bb0():
    "func.return"() : () -> ()
  }) : () -> ()

  // A malformed visibility attribute stays in the attribute dictionary.
  "func.func"() <{function_type = () -> (), sym_name = "bad_visibility", sym_visibility = 1 : i32}> ({
  ^bb0():
    "func.return"() : () -> ()
  }) : () -> ()

  // A symbol name that requires escaping.
  "func.func"() <{function_type = () -> (), sym_name = "name with spaces"}> ({
  ^bb0():
    "func.return"() : () -> ()
  }) : () -> ()

  // External function: no entry block, so argument types print without SSA names.
  "func.func"() <{function_type = (i32, f32) -> i64, sym_name = "external"}> ({}) : () -> ()

  // External function whose single result is itself a function type: parenthesized.
  "func.func"() <{function_type = () -> (() -> i32), sym_name = "fn_res"}> ({}) : () -> ()

  // Default visibility is omitted.
  "func.func"() <{function_type = () -> (), sym_name = "pub_fn", sym_visibility = "public"}> ({
  ^bb0():
    "func.return"() : () -> ()
  }) : () -> ()

  // Multiple results.
  "func.func"() <{function_type = (i1, i8) -> (i32, i64), sym_name = "multi_result"}> ({
  ^bb0(%x: i1, %y: i8):
    %a = "test.test"() : () -> i32
    %b = "test.test"() : () -> i64
    "func.return"(%a, %b) : (i32, i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      func.func @identity(%arg{{[0-9]+_[0-9]+}}: i32) -> i32 {
// CHECK:      func.func private @private_fn(%arg{{[0-9]+_[0-9]+}}: i64) -> i64 attributes {"extra" = 7 : i64} {
// CHECK:      func.func nested @nested_fn() {
// CHECK:      func.func @bad_visibility() attributes {"sym_visibility" = 1 : i32} {
// CHECK:      func.func @"name with spaces"() {
// CHECK:      func.func @external(i32, f32) -> i64
// CHECK:      func.func @fn_res() -> (() -> i32)
// CHECK:      func.func @pub_fn() {
// CHECK:      func.func @multi_result(%arg{{[0-9]+_[0-9]+}}: i1, %arg{{[0-9]+_[0-9]+}}: i8) -> (i32, i64) {
