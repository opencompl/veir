// REQUIRES: llzk-opt
// RUN: %scripts/llzk-diff.sh %s
//
// Function dialect differential (Phase F.5 follow-up, added 2026-05-20).
// Closes the original F.5.2 scope item from `harness/regions-design.md`,
// which called for a Test/LLZK/Function/differential/ test alongside the
// identity + invalid pair.
//
// Exercises the three current shapes of `function.def`:
//   - empty body with no args and no results
//   - one-arg passthrough (block argument used as operand of function.return)
//   - multi-arg with a non-void return signature
//
// Module carries `llzk.lang` so LLZK's parent checks accept it.
// No `function.allow_*` attrs are needed: function.def itself does not
// require them (those gate non-native-field ops, constraints, witness
// emission — see harness/porting-notes.md §Gotcha 6).
//
// Block-argument round-trip: the normalizer in scripts/llzk-diff.sh
// strips VEIR's `^N():` empty-block headers and the cosmetic
// `(%name : type)` → `(%name: type)` space, so the surviving block
// labels number consistently across both sides.

"builtin.module"() ({
  "function.def"() <{sym_name = "empty", function_type = () -> ()}> ({
    "function.return"() : () -> ()
  }) : () -> ()
  "function.def"() <{sym_name = "passthrough", function_type = (!felt.type) -> ()}> ({
  ^entry(%x: !felt.type):
    "function.return"() : () -> ()
  }) : () -> ()
  "function.def"() <{sym_name = "swap", function_type = (!felt.type, !felt.type) -> (!felt.type, !felt.type)}> ({
  ^entry(%a: !felt.type, %b: !felt.type):
    "function.return"(%b, %a) : (!felt.type, !felt.type) -> ()
  }) : () -> ()
}) {llzk.lang} : () -> ()
