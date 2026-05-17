// REQUIRES: llzk-opt
// RUN: %scripts/llzk-diff.sh %s --allowlist %s.allowlist
//
// RAM load/store wrapped in a function.def. ram.load / ram.store
// carry the WitnessGen trait, so the surrounding function needs
// `function.allow_witness`; cast.toindex (used to convert felt to
// index for the addr operand) is NotFieldNative, hence also
// `function.allow_non_native_field_ops`.
//
// Lifted from XFAIL at Phase F.5 (2026-05-18) once function.def
// landed.

"builtin.module"() ({
  "function.def"() <{sym_name = "ram_ops", function_type = () -> ()}> ({
    %b = "arith.constant"() <{value = 1 : i1}> : () -> i1
    %val = "cast.tofelt"(%b) : (i1) -> !felt.type
    %addr = "cast.toindex"(%val) : (!felt.type) -> index
    "ram.store"(%addr, %val) : (index, !felt.type) -> ()
    %0 = "ram.load"(%addr) : (index) -> !felt.type
    "function.return"() : () -> ()
  }) {function.allow_non_native_field_ops, function.allow_witness} : () -> ()
}) : () -> ()
