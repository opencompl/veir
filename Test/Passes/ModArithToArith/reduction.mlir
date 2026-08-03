// RUN: veir-opt %s -p=mod-arith-to-arith | filecheck %s

// Range analysis assumes inputs are already in canonical form, so each input
// value is fixed to have range `[0, q)`.

"builtin.module"() ({
  "func.func"() <{function_type = (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>, sym_name = "mod_arith_add_chain"}> ({
  ^bb0(%a : !mod_arith.int<12289 : i32>, %b : !mod_arith.int<12289 : i32>):
    %c = "mod_arith.constant"() <{"value" = 46 : i32}> : () -> !mod_arith.int<12289 : i32>
    %small = "mod_arith.constant"() <{"value" = 3 : i32}> : () -> !mod_arith.int<12289 : i32>
    %add0 = "mod_arith.add"(%a, %c) {"reduction" = "none"} : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    %add1 = "mod_arith.add"(%add0, %b) {"reduction" = "barrett"} : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    %add2 = "mod_arith.add"(%add1, %a) {"reduction" = "full"} : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    %out = "mod_arith.mul"(%add2, %small) : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    "func.return"(%out) : (!mod_arith.int<12289 : i32>) -> ()

    // CHECK:      "func.func"() <{"function_type" = (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>, "sym_name" = "mod_arith_add_chain"}> ({
    // CHECK-NEXT: ^{{.*}}([[A:%.*]] : !mod_arith.int<12289 : i32>, [[B:%.*]] : !mod_arith.int<12289 : i32>):
    // CHECK-NEXT:   [[C46:%.*]] = "arith.constant"() <{"value" = 46 : i32}> : () -> i32
    // CHECK-NEXT:   [[C46_MOD:%.*]] = "builtin.unrealized_conversion_cast"([[C46]]) : (i32) -> !mod_arith.int<12289 : i32>
    // CHECK-NEXT:   [[C3:%.*]] = "arith.constant"() <{"value" = 3 : i32}> : () -> i32
    // CHECK-NEXT:   [[C3_MOD:%.*]] = "builtin.unrealized_conversion_cast"([[C3]]) : (i32) -> !mod_arith.int<12289 : i32>
    // CHECK-NEXT:   [[A0:%.*]] = "builtin.unrealized_conversion_cast"([[A]]) : (!mod_arith.int<12289 : i32>) -> i32
    // CHECK-NEXT:   [[A0_EXT:%.*]] = "arith.extui"([[A0]]) : (i32) -> i33
    // CHECK-NEXT:   [[C46_INT:%.*]] = "builtin.unrealized_conversion_cast"([[C46_MOD]]) : (!mod_arith.int<12289 : i32>) -> i32
    // CHECK-NEXT:   [[C46_EXT:%.*]] = "arith.extui"([[C46_INT]]) : (i32) -> i33
    // CHECK-NEXT:   [[ADD0:%.*]] = "arith.addi"([[A0_EXT]], [[C46_EXT]]) : (i33, i33) -> i33
    // CHECK-NEXT:   [[ADD0_TRUNC:%.*]] = "arith.trunci"([[ADD0]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i33) -> i32
    // CHECK-NEXT:   [[ADD0_MOD:%.*]] = "builtin.unrealized_conversion_cast"([[ADD0_TRUNC]]) : (i32) -> !mod_arith.int<12289 : i32>
    // CHECK-NEXT:   [[ADD0_INT:%.*]] = "builtin.unrealized_conversion_cast"([[ADD0_MOD]]) : (!mod_arith.int<12289 : i32>) -> i32
    // CHECK-NEXT:   [[ADD0_EXT:%.*]] = "arith.extui"([[ADD0_INT]]) : (i32) -> i33
    // CHECK-NEXT:   [[B_INT:%.*]] = "builtin.unrealized_conversion_cast"([[B]]) : (!mod_arith.int<12289 : i32>) -> i32
    // CHECK-NEXT:   [[B_EXT:%.*]] = "arith.extui"([[B_INT]]) : (i32) -> i33
    // CHECK-NEXT:   [[ADD1:%.*]] = "arith.addi"([[ADD0_EXT]], [[B_EXT]]) : (i33, i33) -> i33
    // CHECK-NEXT:   [[ADD1_WIDE:%.*]] = "arith.extui"([[ADD1]]) : (i33) -> i42
    // CHECK-NEXT:   [[BQ:%.*]] = "arith.constant"() <{"value" = 12289 : i42}> : () -> i42
    // CHECK-NEXT:   [[BMU:%.*]] = "arith.constant"() <{"value" = 21843 : i42}> : () -> i42
    // CHECK-NEXT:   [[BSHIFT:%.*]] = "arith.constant"() <{"value" = 28 : i42}> : () -> i42
    // CHECK-NEXT:   [[BPRODUCT:%.*]] = "arith.muli"([[ADD1_WIDE]], [[BMU]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i42, i42) -> i42
    // CHECK-NEXT:   [[BREDUCED:%.*]] = "arith.shrui"([[BPRODUCT]], [[BSHIFT]]) : (i42, i42) -> i42
    // CHECK-NEXT:   [[BREDUCED_Q:%.*]] = "arith.muli"([[BREDUCED]], [[BQ]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i42, i42) -> i42
    // CHECK-NEXT:   [[BREM:%.*]] = "arith.subi"([[ADD1_WIDE]], [[BREDUCED_Q]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i42, i42) -> i42
    // CHECK-NEXT:   [[BGE:%.*]] = "arith.cmpi"([[BREM]], [[BQ]]) <{"predicate" = 9 : i64}> : (i42, i42) -> i1
    // CHECK-NEXT:   [[BREM_Q:%.*]] = "arith.subi"([[BREM]], [[BQ]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i42, i42) -> i42
    // CHECK-NEXT:   [[BSELECT:%.*]] = "arith.select"([[BGE]], [[BREM_Q]], [[BREM]]) : (i1, i42, i42) -> i42
    // CHECK-NEXT:   [[BTRUNC:%.*]] = "arith.trunci"([[BSELECT]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i42) -> i33
    // CHECK-NEXT:   [[ADD1_TRUNC:%.*]] = "arith.trunci"([[BTRUNC]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i33) -> i32
    // CHECK-NEXT:   [[ADD1_MOD:%.*]] = "builtin.unrealized_conversion_cast"([[ADD1_TRUNC]]) : (i32) -> !mod_arith.int<12289 : i32>
    // CHECK-NEXT:   [[ADD1_INT:%.*]] = "builtin.unrealized_conversion_cast"([[ADD1_MOD]]) : (!mod_arith.int<12289 : i32>) -> i32
    // CHECK-NEXT:   [[ADD1_EXT:%.*]] = "arith.extui"([[ADD1_INT]]) : (i32) -> i33
    // CHECK-NEXT:   [[A2:%.*]] = "builtin.unrealized_conversion_cast"([[A]]) : (!mod_arith.int<12289 : i32>) -> i32
    // CHECK-NEXT:   [[A2_EXT:%.*]] = "arith.extui"([[A2]]) : (i32) -> i33
    // CHECK-NEXT:   [[ADD2:%.*]] = "arith.addi"([[ADD1_EXT]], [[A2_EXT]]) : (i33, i33) -> i33
    // CHECK-NEXT:   [[Q1:%.*]] = "arith.constant"() <{"value" = 12289 : i33}> : () -> i33
    // CHECK-NEXT:   [[ADD2_RED:%.*]] = "arith.remui"([[ADD2]], [[Q1]]) : (i33, i33) -> i33
    // CHECK-NEXT:   [[ADD2_TRUNC:%.*]] = "arith.trunci"([[ADD2_RED]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i33) -> i32
    // CHECK-NEXT:   [[ADD2_MOD:%.*]] = "builtin.unrealized_conversion_cast"([[ADD2_TRUNC]]) : (i32) -> !mod_arith.int<12289 : i32>
    // CHECK-NEXT:   [[ADD2_INT:%.*]] = "builtin.unrealized_conversion_cast"([[ADD2_MOD]]) : (!mod_arith.int<12289 : i32>) -> i32
    // CHECK-NEXT:   [[ADD2_EXT:%.*]] = "arith.extui"([[ADD2_INT]]) : (i32) -> i64
    // CHECK-NEXT:   [[C3_INT:%.*]] = "builtin.unrealized_conversion_cast"([[C3_MOD]]) : (!mod_arith.int<12289 : i32>) -> i32
    // CHECK-NEXT:   [[C3_EXT:%.*]] = "arith.extui"([[C3_INT]]) : (i32) -> i64
    // CHECK-NEXT:   [[PROD:%.*]] = "arith.muli"([[ADD2_EXT]], [[C3_EXT]]) : (i64, i64) -> i64
    // CHECK-NEXT:   [[Q2:%.*]] = "arith.constant"() <{"value" = 12289 : i64}> : () -> i64
    // CHECK-NEXT:   [[PROD_RED:%.*]] = "arith.remui"([[PROD]], [[Q2]]) : (i64, i64) -> i64
    // CHECK-NEXT:   [[PROD_TRUNC:%.*]] = "arith.trunci"([[PROD_RED]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i64) -> i32
    // CHECK-NEXT:   [[OUT:%.*]] = "builtin.unrealized_conversion_cast"([[PROD_TRUNC]]) : (i32) -> !mod_arith.int<12289 : i32>
    // CHECK-NEXT:   "func.return"([[OUT]]) : (!mod_arith.int<12289 : i32>) -> ()
  }) : () -> ()
}) : () -> ()
