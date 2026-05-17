// REQUIRES: llzk-opt
// RUN: %scripts/llzk-diff.sh %s --allowlist %s.allowlist
//
// Bool basic ops wrapped in a function.def carrying
// `function.allow_non_native_field_ops` (the LLZK discardable attr
// gating non-native-field ops). Without the wrapper LLZK rejects
// every bool.* op; without the attribute the wrapper itself is
// rejected.
//
// Phase F.5 (2026-05-18) lifted this from XFAIL after function.def
// landed.

"builtin.module"() ({
  "function.def"() <{sym_name = "bool_ops", function_type = () -> ()}> ({
    %a = "arith.constant"() <{value = 1 : i1}> : () -> i1
    %b = "arith.constant"() <{value = 0 : i1}> : () -> i1
    %0 = "bool.and"(%a, %b) : (i1, i1) -> i1
    %1 = "bool.or"(%a, %b) : (i1, i1) -> i1
    %2 = "bool.xor"(%a, %b) : (i1, i1) -> i1
    %3 = "bool.not"(%a) : (i1) -> i1
    "bool.assert"(%0) : (i1) -> ()
    "bool.assert"(%0) <{msg = "expected true"}> : (i1) -> ()
    "function.return"() : () -> ()
  }) {function.allow_non_native_field_ops} : () -> ()
}) : () -> ()
