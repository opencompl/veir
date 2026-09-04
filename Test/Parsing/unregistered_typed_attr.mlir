// RUN: VEIR_UNREGISTERED_ROUNDTRIP

// Attributes from unregistered dialects may omit the `<body>` and may carry a
// trailing `: type`, as MLIR's generic parser allows for any dialect attribute.
// The type may be builtin or itself unregistered, and the attribute may appear
// in properties, discardable attributes, and nested containers.
"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
    "unregistered.op_one"() {foo = #foo.bar} : () -> ()
    "unregistered.op_two"() {foo = #foo.bar<baz> : i32} : () -> ()
    "unregistered.op_three"() {foo = #foo.zero : !foo.ty} : () -> ()
    %0 = "unregistered.op_four"() <{value = #foo.int<1> : !foo.int<s, 32>}> : () -> !foo.int<s, 32>
    "unregistered.op_five"() {foo = [#foo.bar<1> : i32, #foo.bar<2> : !foo.ptr<!foo.int<s, 32>>]} : () -> ()
    "unregistered.op_six"() {foo = {a = #foo.bar : i64, b = #foo.bar<2> : (i32) -> i32}} : () -> ()
    // CHECK:      "unregistered.op_one"() {"foo" = #foo.bar} : () -> ()
    // CHECK-NEXT: "unregistered.op_two"() {"foo" = #foo.bar<baz> : i32} : () -> ()
    // CHECK-NEXT: "unregistered.op_three"() {"foo" = #foo.zero : !foo.ty} : () -> ()
    // CHECK-NEXT: %{{.*}} = "unregistered.op_four"() <{"value" = #foo.int<1> : !foo.int<s, 32>}> : () -> !foo.int<s, 32>
    // CHECK-NEXT: "unregistered.op_five"() {"foo" = [#foo.bar<1> : i32, #foo.bar<2> : !foo.ptr<!foo.int<s, 32>>]} : () -> ()
    // CHECK-NEXT: "unregistered.op_six"() {"foo" = {"a" = #foo.bar : i64, "b" = #foo.bar<2> : (i32) -> i32}} : () -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
