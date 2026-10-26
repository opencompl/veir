// RUN: veir-opt %s -p=canonicalize | filecheck %s

// mod_arith constants are reduced to their canonical representative in [0, q).
"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
    // A positive value larger than the modulus is reduced.
    %positive = "mod_arith.constant"() <{"value" = 37 : ui8}> : () -> !mod_arith.int<17 : ui8>
    // CHECK: %[[POSITIVE:.*]] = "mod_arith.constant"() <{"value" = 3 : ui8}> : () -> !mod_arith.int<17 : ui8>

    // Euclidean remainder maps a negative value into [0, q).
    %negative = "mod_arith.constant"() <{"value" = -1 : i8}> : () -> !mod_arith.int<17 : ui8>
    // CHECK-NEXT: %[[NEGATIVE:.*]] = "mod_arith.constant"() <{"value" = 16 : ui8}> : () -> !mod_arith.int<17 : ui8>

    // Exact negative multiples become zero. Reduced values take the modulus type.
    %multiple = "mod_arith.constant"() <{"value" = -34 : i16}> : () -> !mod_arith.int<17 : ui8>
    // CHECK-NEXT: %[[MULTIPLE:.*]] = "mod_arith.constant"() <{"value" = 0 : ui8}> : () -> !mod_arith.int<17 : ui8>

    // An already-canonical value is unchanged.
    %canonical = "mod_arith.constant"() <{"value" = 7 : ui64}> : () -> !mod_arith.int<17 : ui8>
    // CHECK-NEXT: %[[CANONICAL:.*]] = "mod_arith.constant"() <{"value" = 7 : ui64}> : () -> !mod_arith.int<17 : ui8>

    "test.test"(%positive, %negative, %multiple, %canonical)
      : (!mod_arith.int<17 : ui8>, !mod_arith.int<17 : ui8>,
         !mod_arith.int<17 : ui8>, !mod_arith.int<17 : ui8>) -> ()
    // CHECK-NEXT: "test.test"(%[[POSITIVE]], %[[NEGATIVE]], %[[MULTIPLE]], %[[CANONICAL]])
    "func.return"() : () -> ()
    // CHECK-NEXT: "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
