// REQUIRES: llzk-opt
// RUN: %scripts/llzk-diff.sh %s
//
// Global ops at module level plus a function wrapping the write
// (LLZK's global.write requires a function.def with
// `function.allow_witness`). The module carries `llzk.lang` because
// LLZK's `global.read`/`global.write` ancestor check rejects an
// unnamed `builtin.module` without that marker.
//
// sym_name is StringAttr (per LLZK ODS); name_ref is
// FlatSymbolRefAttr (the `@`-prefix form). Uses !felt.type for the
// global type — LLZK requires the global's type to be an "LLZK
// type". Lifted from XFAIL at Phase F.5 (2026-05-18) once
// function.def landed.

"builtin.module"() ({
  "global.def"() <{sym_name = "counter", type = !felt.type}> : () -> ()
  "global.def"() <{sym_name = "mutable", type = !felt.type}> : () -> ()
  "function.def"() <{sym_name = "main", function_type = () -> ()}> ({
    %v = "global.read"() <{name_ref = @counter}> : () -> !felt.type
    "global.write"(%v) <{name_ref = @mutable}> : (!felt.type) -> ()
    "function.return"() : () -> ()
  }) {function.allow_witness} : () -> ()
}) {llzk.lang} : () -> ()
