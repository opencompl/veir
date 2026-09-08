// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP
//
// A fence orders other accesses rather than performing one, so only the four
// orderings that say something are allowed, and all four are here: 4 is
// `acquire`, 5 `release`, 6 `acq_rel` and 7 `seq_cst`. The weaker orderings
// -- 0 `not_atomic`, 1 `unordered`, 2 `monotonic` -- are rejected, as is 3,
// which MLIR leaves unused. Each is refused by its own test in Test/Verifier.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void ()>, linkage = #llvm.linkage<external>, sym_name = "barriers"}> ({
    "llvm.fence"() <{ordering = 4 : i64}> : () -> ()
    "llvm.fence"() <{ordering = 5 : i64}> : () -> ()
    "llvm.fence"() <{ordering = 6 : i64}> : () -> ()
    "llvm.fence"() <{ordering = 7 : i64}> : () -> ()
    // Narrowed to a single thread.
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.fence"() <{"ordering" = 4 : i64}> : () -> ()
// CHECK: "llvm.fence"() <{"ordering" = 5 : i64}> : () -> ()
// CHECK: "llvm.fence"() <{"ordering" = 6 : i64}> : () -> ()
// CHECK: "llvm.fence"() <{"ordering" = 7 : i64}> : () -> ()
// CHECK: "llvm.fence"() <{"ordering" = 7 : i64, "syncscope" = "singlethread"}> : () -> ()
