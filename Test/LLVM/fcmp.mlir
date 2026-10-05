// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<i1 (f64, f64)>, linkage = #llvm.linkage<external>, sym_name = "compare"}> ({
  ^bb0(%a: f64, %b: f64):
    %_false = "llvm.fcmp"(%a, %b) <{fastmathFlags = #llvm.fastmath<none>, predicate = 0 : i64}> : (f64, f64) -> i1
    %oeq = "llvm.fcmp"(%a, %b) <{fastmathFlags = #llvm.fastmath<none>, predicate = 1 : i64}> : (f64, f64) -> i1
    %ogt = "llvm.fcmp"(%a, %b) <{fastmathFlags = #llvm.fastmath<none>, predicate = 2 : i64}> : (f64, f64) -> i1
    %oge = "llvm.fcmp"(%a, %b) <{fastmathFlags = #llvm.fastmath<none>, predicate = 3 : i64}> : (f64, f64) -> i1
    %olt = "llvm.fcmp"(%a, %b) <{fastmathFlags = #llvm.fastmath<none>, predicate = 4 : i64}> : (f64, f64) -> i1
    %ole = "llvm.fcmp"(%a, %b) <{fastmathFlags = #llvm.fastmath<none>, predicate = 5 : i64}> : (f64, f64) -> i1
    %one = "llvm.fcmp"(%a, %b) <{fastmathFlags = #llvm.fastmath<none>, predicate = 6 : i64}> : (f64, f64) -> i1
    %ord = "llvm.fcmp"(%a, %b) <{fastmathFlags = #llvm.fastmath<none>, predicate = 7 : i64}> : (f64, f64) -> i1
    %ueq = "llvm.fcmp"(%a, %b) <{fastmathFlags = #llvm.fastmath<none>, predicate = 8 : i64}> : (f64, f64) -> i1
    %ugt = "llvm.fcmp"(%a, %b) <{fastmathFlags = #llvm.fastmath<none>, predicate = 9 : i64}> : (f64, f64) -> i1
    %uge = "llvm.fcmp"(%a, %b) <{fastmathFlags = #llvm.fastmath<none>, predicate = 10 : i64}> : (f64, f64) -> i1
    %ult = "llvm.fcmp"(%a, %b) <{fastmathFlags = #llvm.fastmath<none>, predicate = 11 : i64}> : (f64, f64) -> i1
    %ule = "llvm.fcmp"(%a, %b) <{fastmathFlags = #llvm.fastmath<none>, predicate = 12 : i64}> : (f64, f64) -> i1
    %une = "llvm.fcmp"(%a, %b) <{fastmathFlags = #llvm.fastmath<none>, predicate = 13 : i64}> : (f64, f64) -> i1
    %uno = "llvm.fcmp"(%a, %b) <{fastmathFlags = #llvm.fastmath<none>, predicate = 14 : i64}> : (f64, f64) -> i1
    %_true = "llvm.fcmp"(%a, %b) <{fastmathFlags = #llvm.fastmath<none>, predicate = 15 : i64}> : (f64, f64) -> i1
    // Also check the fastmath flags.
    %fast = "llvm.fcmp"(%a, %b) <{fastmathFlags = #llvm.fastmath<nnan>, predicate = 1 : i64}> : (f64, f64) -> i1
    "llvm.return"(%oeq) : (i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.fcmp"({{.*}}) <{"fastmathFlags" = #llvm.fastmath<none>, "predicate" = 0 : i64}> : (f64, f64) -> i1
// CHECK: "llvm.fcmp"({{.*}}) <{"fastmathFlags" = #llvm.fastmath<none>, "predicate" = 1 : i64}> : (f64, f64) -> i1
// CHECK: "llvm.fcmp"({{.*}}) <{"fastmathFlags" = #llvm.fastmath<none>, "predicate" = 2 : i64}> : (f64, f64) -> i1
// CHECK: "llvm.fcmp"({{.*}}) <{"fastmathFlags" = #llvm.fastmath<none>, "predicate" = 3 : i64}> : (f64, f64) -> i1
// CHECK: "llvm.fcmp"({{.*}}) <{"fastmathFlags" = #llvm.fastmath<none>, "predicate" = 4 : i64}> : (f64, f64) -> i1
// CHECK: "llvm.fcmp"({{.*}}) <{"fastmathFlags" = #llvm.fastmath<none>, "predicate" = 5 : i64}> : (f64, f64) -> i1
// CHECK: "llvm.fcmp"({{.*}}) <{"fastmathFlags" = #llvm.fastmath<none>, "predicate" = 6 : i64}> : (f64, f64) -> i1
// CHECK: "llvm.fcmp"({{.*}}) <{"fastmathFlags" = #llvm.fastmath<none>, "predicate" = 7 : i64}> : (f64, f64) -> i1
// CHECK: "llvm.fcmp"({{.*}}) <{"fastmathFlags" = #llvm.fastmath<none>, "predicate" = 8 : i64}> : (f64, f64) -> i1
// CHECK: "llvm.fcmp"({{.*}}) <{"fastmathFlags" = #llvm.fastmath<none>, "predicate" = 9 : i64}> : (f64, f64) -> i1
// CHECK: "llvm.fcmp"({{.*}}) <{"fastmathFlags" = #llvm.fastmath<none>, "predicate" = 10 : i64}> : (f64, f64) -> i1
// CHECK: "llvm.fcmp"({{.*}}) <{"fastmathFlags" = #llvm.fastmath<none>, "predicate" = 11 : i64}> : (f64, f64) -> i1
// CHECK: "llvm.fcmp"({{.*}}) <{"fastmathFlags" = #llvm.fastmath<none>, "predicate" = 12 : i64}> : (f64, f64) -> i1
// CHECK: "llvm.fcmp"({{.*}}) <{"fastmathFlags" = #llvm.fastmath<none>, "predicate" = 13 : i64}> : (f64, f64) -> i1
// CHECK: "llvm.fcmp"({{.*}}) <{"fastmathFlags" = #llvm.fastmath<none>, "predicate" = 14 : i64}> : (f64, f64) -> i1
// CHECK: "llvm.fcmp"({{.*}}) <{"fastmathFlags" = #llvm.fastmath<none>, "predicate" = 15 : i64}> : (f64, f64) -> i1
// CHECK: "llvm.fcmp"({{.*}}) <{"fastmathFlags" = #llvm.fastmath<nnan>, "predicate" = 1 : i64}> : (f64, f64) -> i1
