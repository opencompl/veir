// RUN: VEIR_UNREGISTERED_ROUNDTRIP
//
// Lossless round-trip of an `llvm.func` carrying both modelled properties
// (`sym_name`, `function_type`) and unmodelled ones (`CConv`, `linkage`,
// `visibility_`). The latter are preserved verbatim via the `extra`
// catch-all dictionary in `LLVMFuncProperties`.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "f", function_type = !llvm.func<i32 (i32)>, CConv = #llvm.cconv<ccc>, linkage = #llvm.linkage<external>, visibility_ = 0 : i64}> ({
  ^bb0(%arg0: i32):
    "llvm.return"(%arg0) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "llvm.func"() <{
// CHECK-SAME:   "CConv" = #llvm.cconv<ccc>
// CHECK-SAME:   "function_type" = !llvm.func<i32 (i32)>
// CHECK-SAME:   "linkage" = #llvm.linkage<external>
// CHECK-SAME:   "sym_name" = "f"
// CHECK-SAME:   "visibility_" = 0 : i64
// CHECK-SAME: }> ({
