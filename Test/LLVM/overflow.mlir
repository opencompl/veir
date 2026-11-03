// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

// Each intrinsic returns one struct, including for fixed-length vectors.
// Use odd integer widths as well as i1 to exercise the overloaded types.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (i32, i32)>, sym_name = "scalar"}> ({
  ^bb0(%a: i32, %b: i32):
    %sadd = "llvm.intr.sadd.with.overflow"(%a, %b) : (i32, i32) -> !llvm.struct<(i32, i1)>
    // CHECK: "llvm.intr.sadd.with.overflow"({{.*}}) : (i32, i32) -> !llvm.struct<(i32, i1)>
    %uadd = "llvm.intr.uadd.with.overflow"(%a, %b) : (i32, i32) -> !llvm.struct<(i32, i1)>
    // CHECK: "llvm.intr.uadd.with.overflow"({{.*}}) : (i32, i32) -> !llvm.struct<(i32, i1)>
    %ssub = "llvm.intr.ssub.with.overflow"(%a, %b) : (i32, i32) -> !llvm.struct<(i32, i1)>
    // CHECK: "llvm.intr.ssub.with.overflow"({{.*}}) : (i32, i32) -> !llvm.struct<(i32, i1)>
    %usub = "llvm.intr.usub.with.overflow"(%a, %b) : (i32, i32) -> !llvm.struct<(i32, i1)>
    // CHECK: "llvm.intr.usub.with.overflow"({{.*}}) : (i32, i32) -> !llvm.struct<(i32, i1)>
    %smul = "llvm.intr.smul.with.overflow"(%a, %b) : (i32, i32) -> !llvm.struct<(i32, i1)>
    // CHECK: "llvm.intr.smul.with.overflow"({{.*}}) : (i32, i32) -> !llvm.struct<(i32, i1)>
    %umul = "llvm.intr.umul.with.overflow"(%a, %b) : (i32, i32) -> !llvm.struct<(i32, i1)>
    // CHECK: "llvm.intr.umul.with.overflow"({{.*}}) : (i32, i32) -> !llvm.struct<(i32, i1)>
    "llvm.return"() : () -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<void (i1, i1)>, sym_name = "narrow"}> ({
  ^bb0(%a: i1, %b: i1):
    %sadd = "llvm.intr.sadd.with.overflow"(%a, %b) : (i1, i1) -> !llvm.struct<(i1, i1)>
    // CHECK: "llvm.intr.sadd.with.overflow"({{.*}}) : (i1, i1) -> !llvm.struct<(i1, i1)>
    %uadd = "llvm.intr.uadd.with.overflow"(%a, %b) : (i1, i1) -> !llvm.struct<(i1, i1)>
    // CHECK: "llvm.intr.uadd.with.overflow"({{.*}}) : (i1, i1) -> !llvm.struct<(i1, i1)>
    %ssub = "llvm.intr.ssub.with.overflow"(%a, %b) : (i1, i1) -> !llvm.struct<(i1, i1)>
    // CHECK: "llvm.intr.ssub.with.overflow"({{.*}}) : (i1, i1) -> !llvm.struct<(i1, i1)>
    %usub = "llvm.intr.usub.with.overflow"(%a, %b) : (i1, i1) -> !llvm.struct<(i1, i1)>
    // CHECK: "llvm.intr.usub.with.overflow"({{.*}}) : (i1, i1) -> !llvm.struct<(i1, i1)>
    %smul = "llvm.intr.smul.with.overflow"(%a, %b) : (i1, i1) -> !llvm.struct<(i1, i1)>
    // CHECK: "llvm.intr.smul.with.overflow"({{.*}}) : (i1, i1) -> !llvm.struct<(i1, i1)>
    %umul = "llvm.intr.umul.with.overflow"(%a, %b) : (i1, i1) -> !llvm.struct<(i1, i1)>
    // CHECK: "llvm.intr.umul.with.overflow"({{.*}}) : (i1, i1) -> !llvm.struct<(i1, i1)>
    "llvm.return"() : () -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<void (i129, i129)>, sym_name = "wide"}> ({
  ^bb0(%a: i129, %b: i129):
    %sadd = "llvm.intr.sadd.with.overflow"(%a, %b) : (i129, i129) -> !llvm.struct<(i129, i1)>
    // CHECK: "llvm.intr.sadd.with.overflow"({{.*}}) : (i129, i129) -> !llvm.struct<(i129, i1)>
    %uadd = "llvm.intr.uadd.with.overflow"(%a, %b) : (i129, i129) -> !llvm.struct<(i129, i1)>
    // CHECK: "llvm.intr.uadd.with.overflow"({{.*}}) : (i129, i129) -> !llvm.struct<(i129, i1)>
    %ssub = "llvm.intr.ssub.with.overflow"(%a, %b) : (i129, i129) -> !llvm.struct<(i129, i1)>
    // CHECK: "llvm.intr.ssub.with.overflow"({{.*}}) : (i129, i129) -> !llvm.struct<(i129, i1)>
    %usub = "llvm.intr.usub.with.overflow"(%a, %b) : (i129, i129) -> !llvm.struct<(i129, i1)>
    // CHECK: "llvm.intr.usub.with.overflow"({{.*}}) : (i129, i129) -> !llvm.struct<(i129, i1)>
    %smul = "llvm.intr.smul.with.overflow"(%a, %b) : (i129, i129) -> !llvm.struct<(i129, i1)>
    // CHECK: "llvm.intr.smul.with.overflow"({{.*}}) : (i129, i129) -> !llvm.struct<(i129, i1)>
    %umul = "llvm.intr.umul.with.overflow"(%a, %b) : (i129, i129) -> !llvm.struct<(i129, i1)>
    // CHECK: "llvm.intr.umul.with.overflow"({{.*}}) : (i129, i129) -> !llvm.struct<(i129, i1)>
    "llvm.return"() : () -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<void (vector<4xi17>, vector<4xi17>)>, sym_name = "fixed"}> ({
  ^bb0(%a: vector<4xi17>, %b: vector<4xi17>):
    %sadd = "llvm.intr.sadd.with.overflow"(%a, %b) : (vector<4xi17>, vector<4xi17>) -> !llvm.struct<(vector<4xi17>, vector<4xi1>)>
    // CHECK: "llvm.intr.sadd.with.overflow"({{.*}}) : (vector<4xi17>, vector<4xi17>) -> !llvm.struct<(vector<4xi17>, vector<4xi1>)>
    %uadd = "llvm.intr.uadd.with.overflow"(%a, %b) : (vector<4xi17>, vector<4xi17>) -> !llvm.struct<(vector<4xi17>, vector<4xi1>)>
    // CHECK: "llvm.intr.uadd.with.overflow"({{.*}}) : (vector<4xi17>, vector<4xi17>) -> !llvm.struct<(vector<4xi17>, vector<4xi1>)>
    %ssub = "llvm.intr.ssub.with.overflow"(%a, %b) : (vector<4xi17>, vector<4xi17>) -> !llvm.struct<(vector<4xi17>, vector<4xi1>)>
    // CHECK: "llvm.intr.ssub.with.overflow"({{.*}}) : (vector<4xi17>, vector<4xi17>) -> !llvm.struct<(vector<4xi17>, vector<4xi1>)>
    %usub = "llvm.intr.usub.with.overflow"(%a, %b) : (vector<4xi17>, vector<4xi17>) -> !llvm.struct<(vector<4xi17>, vector<4xi1>)>
    // CHECK: "llvm.intr.usub.with.overflow"({{.*}}) : (vector<4xi17>, vector<4xi17>) -> !llvm.struct<(vector<4xi17>, vector<4xi1>)>
    %smul = "llvm.intr.smul.with.overflow"(%a, %b) : (vector<4xi17>, vector<4xi17>) -> !llvm.struct<(vector<4xi17>, vector<4xi1>)>
    // CHECK: "llvm.intr.smul.with.overflow"({{.*}}) : (vector<4xi17>, vector<4xi17>) -> !llvm.struct<(vector<4xi17>, vector<4xi1>)>
    %umul = "llvm.intr.umul.with.overflow"(%a, %b) : (vector<4xi17>, vector<4xi17>) -> !llvm.struct<(vector<4xi17>, vector<4xi1>)>
    // CHECK: "llvm.intr.umul.with.overflow"({{.*}}) : (vector<4xi17>, vector<4xi17>) -> !llvm.struct<(vector<4xi17>, vector<4xi1>)>
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
