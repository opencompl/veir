// RUN: VEIR_ROUNDTRIP

// `mod_arith` is exempt from the parser's MLIR-style normalization of integer
// literals: Veir reads its moduli and constants as mathematical integers, so
// they are kept exactly as written. This deliberately differs from HEIR, which
// treats them as bit patterns and requires a spare bit in the storage type.
//
//   - A modulus may fill its whole storage type (`251 : i8`, `7 : i3`), where
//     normalization would make it negative.
//   - `250 : i8` is 250, not -6, and `-3 : i32` is -3, reduced mod q later.
//
// Only the properties of `mod_arith` operations are exempt; a discardable
// attribute on one is normalized like any other.

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
    %0 = "mod_arith.constant"() <{value = 250 : i8}> : () -> !mod_arith.int<251 : i8>
    %1 = "mod_arith.constant"() <{value = 5 : i3}> : () -> !mod_arith.int<7 : i3>
    %2 = "mod_arith.constant"() <{value = -3 : i32}> : () -> !mod_arith.int<17 : i32>
    %3 = "mod_arith.constant"() <{value = 250 : i8}> {tag = 250 : i8} : () -> !mod_arith.int<251 : i8>
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "mod_arith.constant"() <{"value" = 250 : i8}> : () -> !mod_arith.int<251 : i8>
// CHECK-NEXT: "mod_arith.constant"() <{"value" = 5 : i3}> : () -> !mod_arith.int<7 : i3>
// CHECK-NEXT: "mod_arith.constant"() <{"value" = -3 : i32}> : () -> !mod_arith.int<17 : i32>
// CHECK-NEXT: "mod_arith.constant"() <{"value" = 250 : i8}> {"tag" = -6 : i8} : () -> !mod_arith.int<251 : i8>
