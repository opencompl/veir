// REQUIRES: llzk-opt
// RUN: %scripts/llzk-diff.sh %s --allowlist %s.allowlist
//
// Casts: i1 -> felt -> index. LLZK's cast.tofelt only accepts i1 or
// index inputs (the i32 case our identity.mlir uses works in VEIR
// because VEIR doesn't enforce the operand-type predicate — a
// documented coverage gap).
//
// Wrapped in function.def with function.allow_non_native_field_ops
// (cast.toindex is NotFieldNative). Lifted from XFAIL at Phase F.5
// (2026-05-18) once function.def landed.

"builtin.module"() ({
  "function.def"() <{sym_name = "casts", function_type = () -> ()}> ({
    %b = "arith.constant"() <{value = 1 : i1}> : () -> i1
    %f = "cast.tofelt"(%b) : (i1) -> !felt.type
    %i = "cast.toindex"(%f) : (!felt.type) -> index
    "function.return"() : () -> ()
  }) {function.allow_non_native_field_ops} : () -> ()
}) : () -> ()
