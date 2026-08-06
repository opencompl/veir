// RUN: veir-opt %s -p=mod-arith | filecheck %s

// The `mod-arith` pass group lowers `mod_arith` all the way to `arith`:
// ops are lowered, `!mod_arith.int` function boundaries are coerced to their
// storage integer type, the resulting cast round trips are reconciled away,
// and `arith.remui` is rewritten to Barrett reduction.

"builtin.module"() ({
  "func.func"() <{function_type = (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>, sym_name = "chain"}> ({
  ^bb0(%a : !mod_arith.int<12289 : i32>, %b : !mod_arith.int<12289 : i32>):
    %c5 = "mod_arith.constant"() <{"value" = 5 : i32}> : () -> !mod_arith.int<12289 : i32>
    %s = "mod_arith.add"(%a, %b) : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    %d = "mod_arith.sub"(%a, %b) : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    %m = "mod_arith.mul"(%s, %d) : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    %r = "mod_arith.mul"(%m, %c5) : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    %out = "mod_arith.add"(%r, %a) : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    "func.return"(%out) : (!mod_arith.int<12289 : i32>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "func.func"() <{"function_type" = (i32, i32) -> i32, "sym_name" = "chain"}> ({
// CHECK-NEXT:   ^{{.*}}([[A:%.*]] : i32, [[B:%.*]] : i32):

// The mod_arith.constant, and both arguments extended
// CHECK-NEXT:     [[C5:%.*]] = "arith.constant"() <{"value" = 5 : i32}> : () -> i32
// CHECK-NEXT:     [[A33:%.*]] = "arith.extui"([[A]]) : (i32) -> i33
// CHECK-NEXT:     [[B33:%.*]] = "arith.extui"([[B]]) : (i32) -> i33

// s = (a + b) mod q: i33 add
// CHECK-NEXT:     [[SUM:%.*]] = "arith.addi"([[A33]], [[B33]]) : (i33, i33) -> i33
// CHECK-NEXT:     [[SUMW:%.*]] = "arith.extui"([[SUM]]) : (i33) -> i42
// CHECK-NEXT:     [[Q42:%.*]] = "arith.constant"() <{"value" = 12289 : i42}> : () -> i42
// CHECK-NEXT:     [[MU42:%.*]] = "arith.constant"() <{"value" = 21843 : i42}> : () -> i42
// CHECK-NEXT:     [[SH42:%.*]] = "arith.constant"() <{"value" = 28 : i42}> : () -> i42
// CHECK-NEXT:     [[P1:%.*]] = "arith.muli"([[SUMW]], [[MU42]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i42, i42) -> i42
// CHECK-NEXT:     [[E1:%.*]] = "arith.shrui"([[P1]], [[SH42]]) : (i42, i42) -> i42
// CHECK-NEXT:     [[EQ1:%.*]] = "arith.muli"([[E1]], [[Q42]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i42, i42) -> i42
// CHECK-NEXT:     [[R1:%.*]] = "arith.subi"([[SUMW]], [[EQ1]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i42, i42) -> i42
// CHECK-NEXT:     [[G1:%.*]] = "arith.cmpi"([[R1]], [[Q42]]) <{"predicate" = 9 : i64}> : (i42, i42) -> i1
// CHECK-NEXT:     [[R1Q:%.*]] = "arith.subi"([[R1]], [[Q42]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i42, i42) -> i42
// CHECK-NEXT:     [[S1:%.*]] = "arith.select"([[G1]], [[R1Q]], [[R1]]) : (i1, i42, i42) -> i42
// CHECK-NEXT:     [[T1:%.*]] = "arith.trunci"([[S1]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i42) -> i33
// CHECK-NEXT:     [[S:%.*]] = "arith.trunci"([[T1]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i33) -> i32

// d = (a - b) mod q
// CHECK-NEXT:     [[Q33:%.*]] = "arith.constant"() <{"value" = 12289 : i33}> : () -> i33
// CHECK-NEXT:     [[AQ:%.*]] = "arith.addi"([[A33]], [[Q33]]) : (i33, i33) -> i33
// CHECK-NEXT:     [[DIF:%.*]] = "arith.subi"([[AQ]], [[B33]]) : (i33, i33) -> i33
// CHECK-NEXT:     [[DIFW:%.*]] = "arith.extui"([[DIF]]) : (i33) -> i42
// CHECK-NEXT:     [[P2:%.*]] = "arith.muli"([[DIFW]], [[MU42]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i42, i42) -> i42
// CHECK-NEXT:     [[E2:%.*]] = "arith.shrui"([[P2]], [[SH42]]) : (i42, i42) -> i42
// CHECK-NEXT:     [[EQ2:%.*]] = "arith.muli"([[E2]], [[Q42]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i42, i42) -> i42
// CHECK-NEXT:     [[R2:%.*]] = "arith.subi"([[DIFW]], [[EQ2]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i42, i42) -> i42
// CHECK-NEXT:     [[G2:%.*]] = "arith.cmpi"([[R2]], [[Q42]]) <{"predicate" = 9 : i64}> : (i42, i42) -> i1
// CHECK-NEXT:     [[R2Q:%.*]] = "arith.subi"([[R2]], [[Q42]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i42, i42) -> i42
// CHECK-NEXT:     [[S2:%.*]] = "arith.select"([[G2]], [[R2Q]], [[R2]]) : (i1, i42, i42) -> i42
// CHECK-NEXT:     [[T2:%.*]] = "arith.trunci"([[S2]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i42) -> i33
// CHECK-NEXT:     [[D:%.*]] = "arith.trunci"([[T2]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i33) -> i32

// m = (s * d) mod q
// CHECK-NEXT:     [[SW:%.*]] = "arith.extui"([[S]]) : (i32) -> i64
// CHECK-NEXT:     [[DW:%.*]] = "arith.extui"([[D]]) : (i32) -> i64
// CHECK-NEXT:     [[M:%.*]] = "arith.muli"([[SW]], [[DW]]) : (i64, i64) -> i64
// CHECK-NEXT:     [[Q64:%.*]] = "arith.constant"() <{"value" = 12289 : i64}> : () -> i64
// CHECK-NEXT:     [[MU64:%.*]] = "arith.constant"() <{"value" = 21843 : i64}> : () -> i64
// CHECK-NEXT:     [[SH64:%.*]] = "arith.constant"() <{"value" = 28 : i64}> : () -> i64
// CHECK-NEXT:     [[P3:%.*]] = "arith.muli"([[M]], [[MU64]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i64, i64) -> i64
// CHECK-NEXT:     [[E3:%.*]] = "arith.shrui"([[P3]], [[SH64]]) : (i64, i64) -> i64
// CHECK-NEXT:     [[EQ3:%.*]] = "arith.muli"([[E3]], [[Q64]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i64, i64) -> i64
// CHECK-NEXT:     [[R3:%.*]] = "arith.subi"([[M]], [[EQ3]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i64, i64) -> i64
// CHECK-NEXT:     [[G3:%.*]] = "arith.cmpi"([[R3]], [[Q64]]) <{"predicate" = 9 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:     [[R3Q:%.*]] = "arith.subi"([[R3]], [[Q64]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i64, i64) -> i64
// CHECK-NEXT:     [[S3:%.*]] = "arith.select"([[G3]], [[R3Q]], [[R3]]) : (i1, i64, i64) -> i64
// CHECK-NEXT:     [[MRED:%.*]] = "arith.trunci"([[S3]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i64) -> i32

// r = (m * 5) mod q
// CHECK-NEXT:     [[MW:%.*]] = "arith.extui"([[MRED]]) : (i32) -> i64
// CHECK-NEXT:     [[C5W:%.*]] = "arith.extui"([[C5]]) : (i32) -> i64
// CHECK-NEXT:     [[M5:%.*]] = "arith.muli"([[MW]], [[C5W]]) : (i64, i64) -> i64
// CHECK-NEXT:     [[P4:%.*]] = "arith.muli"([[M5]], [[MU64]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i64, i64) -> i64
// CHECK-NEXT:     [[E4:%.*]] = "arith.shrui"([[P4]], [[SH64]]) : (i64, i64) -> i64
// CHECK-NEXT:     [[EQ4:%.*]] = "arith.muli"([[E4]], [[Q64]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i64, i64) -> i64
// CHECK-NEXT:     [[R4:%.*]] = "arith.subi"([[M5]], [[EQ4]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i64, i64) -> i64
// CHECK-NEXT:     [[G4:%.*]] = "arith.cmpi"([[R4]], [[Q64]]) <{"predicate" = 9 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:     [[R4Q:%.*]] = "arith.subi"([[R4]], [[Q64]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i64, i64) -> i64
// CHECK-NEXT:     [[S4:%.*]] = "arith.select"([[G4]], [[R4Q]], [[R4]]) : (i1, i64, i64) -> i64
// CHECK-NEXT:     [[RRED:%.*]] = "arith.trunci"([[S4]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i64) -> i32

// out = (r + a) mod q
// CHECK-NEXT:     [[RW:%.*]] = "arith.extui"([[RRED]]) : (i32) -> i33
// CHECK-NEXT:     [[OUT:%.*]] = "arith.addi"([[RW]], [[A33]]) : (i33, i33) -> i33
// CHECK-NEXT:     [[OUTW:%.*]] = "arith.extui"([[OUT]]) : (i33) -> i42
// CHECK-NEXT:     [[P5:%.*]] = "arith.muli"([[OUTW]], [[MU42]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i42, i42) -> i42
// CHECK-NEXT:     [[E5:%.*]] = "arith.shrui"([[P5]], [[SH42]]) : (i42, i42) -> i42
// CHECK-NEXT:     [[EQ5:%.*]] = "arith.muli"([[E5]], [[Q42]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i42, i42) -> i42
// CHECK-NEXT:     [[R5:%.*]] = "arith.subi"([[OUTW]], [[EQ5]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i42, i42) -> i42
// CHECK-NEXT:     [[G5:%.*]] = "arith.cmpi"([[R5]], [[Q42]]) <{"predicate" = 9 : i64}> : (i42, i42) -> i1
// CHECK-NEXT:     [[R5Q:%.*]] = "arith.subi"([[R5]], [[Q42]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i42, i42) -> i42
// CHECK-NEXT:     [[S5:%.*]] = "arith.select"([[G5]], [[R5Q]], [[R5]]) : (i1, i42, i42) -> i42
// CHECK-NEXT:     [[T5:%.*]] = "arith.trunci"([[S5]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i42) -> i33
// CHECK-NEXT:     [[RET:%.*]] = "arith.trunci"([[T5]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i33) -> i32
// CHECK-NEXT:     "func.return"([[RET]]) : (i32) -> ()
// CHECK-NEXT:   }) : () -> ()
// CHECK-NEXT: }) : () -> ()
