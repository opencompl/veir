// REQUIRES: llzk-opt
// RUN: %scripts/llzk-diff.sh %s --allowlist %s.allowlist
//
// Constrain equality wrapped in a function.def with
// `function.allow_constraint` (constrain.eq has ConstraintGen).
// Lifted from XFAIL at Phase F.5 (2026-05-18) once function.def
// landed.

"builtin.module"() ({
  "function.def"() <{sym_name = "constrain", function_type = () -> ()}> ({
    %b = "arith.constant"() <{value = 1 : i1}> : () -> i1
    %a = "cast.tofelt"(%b) : (i1) -> !felt.type
    "constrain.eq"(%a, %a) : (!felt.type, !felt.type) -> ()
    "function.return"() : () -> ()
  }) {function.allow_constraint} : () -> ()
}) : () -> ()
