// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

// Both fields of each scalar overflow result are ordinary extractvalue results.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<i32 (i32, i32)>, sym_name = "sadd"}> ({
  ^bb0(%a: i32, %b: i32):
    %pair = "llvm.intr.sadd.with.overflow"(%a, %b) : (i32, i32) -> !llvm.struct<(i32, i1)>
    // CHECK: "llvm.intr.sadd.with.overflow"
    %value = "llvm.extractvalue"(%pair) <{position = array<i64: 0>}> : (!llvm.struct<(i32, i1)>) -> i32
    // CHECK: "llvm.extractvalue"({{.*}}) <{"position" = array<i64: 0>}> : (!llvm.struct<(i32, i1)>) -> i32
    %overflow = "llvm.extractvalue"(%pair) <{position = array<i64: 1>}> : (!llvm.struct<(i32, i1)>) -> i1
    // CHECK: "llvm.extractvalue"({{.*}}) <{"position" = array<i64: 1>}> : (!llvm.struct<(i32, i1)>) -> i1
    %result = "llvm.select"(%overflow, %a, %value) : (i1, i32, i32) -> i32
    "llvm.return"(%result) : (i32) -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<i32 (i32, i32)>, sym_name = "uadd"}> ({
  ^bb0(%a: i32, %b: i32):
    %pair = "llvm.intr.uadd.with.overflow"(%a, %b) : (i32, i32) -> !llvm.struct<(i32, i1)>
    // CHECK: "llvm.intr.uadd.with.overflow"
    %value = "llvm.extractvalue"(%pair) <{position = array<i64: 0>}> : (!llvm.struct<(i32, i1)>) -> i32
    // CHECK: "llvm.extractvalue"({{.*}}) <{"position" = array<i64: 0>}> : (!llvm.struct<(i32, i1)>) -> i32
    %overflow = "llvm.extractvalue"(%pair) <{position = array<i64: 1>}> : (!llvm.struct<(i32, i1)>) -> i1
    // CHECK: "llvm.extractvalue"({{.*}}) <{"position" = array<i64: 1>}> : (!llvm.struct<(i32, i1)>) -> i1
    %result = "llvm.select"(%overflow, %a, %value) : (i1, i32, i32) -> i32
    "llvm.return"(%result) : (i32) -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<i32 (i32, i32)>, sym_name = "ssub"}> ({
  ^bb0(%a: i32, %b: i32):
    %pair = "llvm.intr.ssub.with.overflow"(%a, %b) : (i32, i32) -> !llvm.struct<(i32, i1)>
    // CHECK: "llvm.intr.ssub.with.overflow"
    %value = "llvm.extractvalue"(%pair) <{position = array<i64: 0>}> : (!llvm.struct<(i32, i1)>) -> i32
    // CHECK: "llvm.extractvalue"({{.*}}) <{"position" = array<i64: 0>}> : (!llvm.struct<(i32, i1)>) -> i32
    %overflow = "llvm.extractvalue"(%pair) <{position = array<i64: 1>}> : (!llvm.struct<(i32, i1)>) -> i1
    // CHECK: "llvm.extractvalue"({{.*}}) <{"position" = array<i64: 1>}> : (!llvm.struct<(i32, i1)>) -> i1
    %result = "llvm.select"(%overflow, %a, %value) : (i1, i32, i32) -> i32
    "llvm.return"(%result) : (i32) -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<i32 (i32, i32)>, sym_name = "usub"}> ({
  ^bb0(%a: i32, %b: i32):
    %pair = "llvm.intr.usub.with.overflow"(%a, %b) : (i32, i32) -> !llvm.struct<(i32, i1)>
    // CHECK: "llvm.intr.usub.with.overflow"
    %value = "llvm.extractvalue"(%pair) <{position = array<i64: 0>}> : (!llvm.struct<(i32, i1)>) -> i32
    // CHECK: "llvm.extractvalue"({{.*}}) <{"position" = array<i64: 0>}> : (!llvm.struct<(i32, i1)>) -> i32
    %overflow = "llvm.extractvalue"(%pair) <{position = array<i64: 1>}> : (!llvm.struct<(i32, i1)>) -> i1
    // CHECK: "llvm.extractvalue"({{.*}}) <{"position" = array<i64: 1>}> : (!llvm.struct<(i32, i1)>) -> i1
    %result = "llvm.select"(%overflow, %a, %value) : (i1, i32, i32) -> i32
    "llvm.return"(%result) : (i32) -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<i32 (i32, i32)>, sym_name = "smul"}> ({
  ^bb0(%a: i32, %b: i32):
    %pair = "llvm.intr.smul.with.overflow"(%a, %b) : (i32, i32) -> !llvm.struct<(i32, i1)>
    // CHECK: "llvm.intr.smul.with.overflow"
    %value = "llvm.extractvalue"(%pair) <{position = array<i64: 0>}> : (!llvm.struct<(i32, i1)>) -> i32
    // CHECK: "llvm.extractvalue"({{.*}}) <{"position" = array<i64: 0>}> : (!llvm.struct<(i32, i1)>) -> i32
    %overflow = "llvm.extractvalue"(%pair) <{position = array<i64: 1>}> : (!llvm.struct<(i32, i1)>) -> i1
    // CHECK: "llvm.extractvalue"({{.*}}) <{"position" = array<i64: 1>}> : (!llvm.struct<(i32, i1)>) -> i1
    %result = "llvm.select"(%overflow, %a, %value) : (i1, i32, i32) -> i32
    "llvm.return"(%result) : (i32) -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<i32 (i32, i32)>, sym_name = "umul"}> ({
  ^bb0(%a: i32, %b: i32):
    %pair = "llvm.intr.umul.with.overflow"(%a, %b) : (i32, i32) -> !llvm.struct<(i32, i1)>
    // CHECK: "llvm.intr.umul.with.overflow"
    %value = "llvm.extractvalue"(%pair) <{position = array<i64: 0>}> : (!llvm.struct<(i32, i1)>) -> i32
    // CHECK: "llvm.extractvalue"({{.*}}) <{"position" = array<i64: 0>}> : (!llvm.struct<(i32, i1)>) -> i32
    %overflow = "llvm.extractvalue"(%pair) <{position = array<i64: 1>}> : (!llvm.struct<(i32, i1)>) -> i1
    // CHECK: "llvm.extractvalue"({{.*}}) <{"position" = array<i64: 1>}> : (!llvm.struct<(i32, i1)>) -> i1
    %result = "llvm.select"(%overflow, %a, %value) : (i1, i32, i32) -> i32
    "llvm.return"(%result) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
