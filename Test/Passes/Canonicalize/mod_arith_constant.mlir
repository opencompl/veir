// RUN: veir-opt %s -p=canonicalize | filecheck %s

// mod_arith constants are reduced to their canonical representative in [0, q).
"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
    // A positive value larger than the modulus is reduced.
    %positive = "mod_arith.constant"() <{"value" = 37 : i8}> : () -> !mod_arith.int<17 : i8>
    // CHECK: %[[POSITIVE:.*]] = "mod_arith.constant"() <{"value" = 3 : i8}> : () -> !mod_arith.int<17 : i8>

    // Euclidean remainder maps a negative value into [0, q).
    %negative = "mod_arith.constant"() <{"value" = -1 : i8}> : () -> !mod_arith.int<17 : i8>
    // CHECK-NEXT: %[[NEGATIVE:.*]] = "mod_arith.constant"() <{"value" = 16 : i8}> : () -> !mod_arith.int<17 : i8>

    // Exact negative multiples become zero. The value attribute's width is preserved.
    %multiple = "mod_arith.constant"() <{"value" = -34 : i16}> : () -> !mod_arith.int<17 : i8>
    // CHECK-NEXT: %[[MULTIPLE:.*]] = "mod_arith.constant"() <{"value" = 0 : i16}> : () -> !mod_arith.int<17 : i8>

    // An already-canonical value is unchanged.
    %canonical = "mod_arith.constant"() <{"value" = 7 : i64}> : () -> !mod_arith.int<17 : i8>
    // CHECK-NEXT: %[[CANONICAL:.*]] = "mod_arith.constant"() <{"value" = 7 : i64}> : () -> !mod_arith.int<17 : i8>

    "test.test"(%positive, %negative, %multiple, %canonical)
      : (!mod_arith.int<17 : i8>, !mod_arith.int<17 : i8>,
         !mod_arith.int<17 : i8>, !mod_arith.int<17 : i8>) -> ()
    // CHECK-NEXT: "test.test"(%[[POSITIVE]], %[[NEGATIVE]], %[[MULTIPLE]], %[[CANONICAL]])
    "func.return"() : () -> ()
    // CHECK-NEXT: "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
