// RUN: veir-opt %s -p=canonicalize | filecheck %s --check-prefix=DEFAULT
// RUN: veir-opt %s -p='canonicalize{mod-arith-constant=false}' | filecheck %s --check-prefix=NO-MOD
// RUN: veir-opt %s -p='canonicalize{commutative-constant-rhs=false}' | filecheck %s --check-prefix=NO-COMMUTE
// RUN: veir-opt %s -p='canonicalize{mod-arith-constant=false commutative-constant-rhs=false}' | filecheck %s --check-prefix=NEITHER

// Both parts of canonicalize default to true and can be disabled independently.
"builtin.module"() ({
  "func.func"() <{function_type = (i32) -> i32, sym_name = "main"}> ({
    ^bb0(%x : i32):
      // DEFAULT:      ^{{.*}}(%[[DEFAULT_X:.*]] : i32):
      // NO-MOD:       ^{{.*}}(%[[NO_MOD_X:.*]] : i32):
      // NO-COMMUTE:   ^{{.*}}(%[[NO_COMMUTE_X:.*]] : i32):
      // NEITHER:      ^{{.*}}(%[[NEITHER_X:.*]] : i32):
      %mod = "mod_arith.constant"() <{"value" = 37 : i8}> : () -> !mod_arith.int<17 : i8>
      // DEFAULT-NEXT:    %[[DEFAULT_MOD:.*]] = "mod_arith.constant"() <{"value" = 3 : i8}>
      // NO-MOD-NEXT:     %[[NO_MOD_MOD:.*]] = "mod_arith.constant"() <{"value" = 37 : i8}>
      // NO-COMMUTE-NEXT: %[[NO_COMMUTE_MOD:.*]] = "mod_arith.constant"() <{"value" = 3 : i8}>
      // NEITHER-NEXT:    %[[NEITHER_MOD:.*]] = "mod_arith.constant"() <{"value" = 37 : i8}>
      %c = "arith.constant"() <{"value" = 5 : i32}> : () -> i32
      // DEFAULT-NEXT:    %[[DEFAULT_C:.*]] = "arith.constant"() <{"value" = 5 : i32}>
      // NO-MOD-NEXT:     %[[NO_MOD_C:.*]] = "arith.constant"() <{"value" = 5 : i32}>
      // NO-COMMUTE-NEXT: %[[NO_COMMUTE_C:.*]] = "arith.constant"() <{"value" = 5 : i32}>
      // NEITHER-NEXT:    %[[NEITHER_C:.*]] = "arith.constant"() <{"value" = 5 : i32}>
      %add = "arith.addi"(%c, %x) : (i32, i32) -> i32
      // DEFAULT-NEXT:    %[[DEFAULT_ADD:.*]] = "arith.addi"(%[[DEFAULT_X]], %[[DEFAULT_C]])
      // NO-MOD-NEXT:     %[[NO_MOD_ADD:.*]] = "arith.addi"(%[[NO_MOD_X]], %[[NO_MOD_C]])
      // NO-COMMUTE-NEXT: %[[NO_COMMUTE_ADD:.*]] = "arith.addi"(%[[NO_COMMUTE_C]], %[[NO_COMMUTE_X]])
      // NEITHER-NEXT:    %[[NEITHER_ADD:.*]] = "arith.addi"(%[[NEITHER_C]], %[[NEITHER_X]])
      "test.test"(%mod) : (!mod_arith.int<17 : i8>) -> ()
      "func.return"(%add) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
