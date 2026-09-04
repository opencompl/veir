// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP
//
// `#llvm.loop_annotation` is the `!llvm.loop` metadata a branch carries back to
// its loop header. It rides on `llvm.br` and `llvm.cond_br`, which is why both
// get LLVM-specific properties: `cf`'s have no room for it, and an attribute
// the properties do not model is dropped rather than round-tripped.
//
// The body is kept verbatim, so the case that matters is the nested one: a
// transformation option is itself written `<...>` and must not end the body.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (i1)>, linkage = #llvm.linkage<external>, sym_name = "loop"}> ({
  ^bb0(%c: i1):
    "llvm.cond_br"(%c)[^bb1, ^bb3] <{loop_annotation = #llvm.loop_annotation<mustProgress = true>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  // A nested option, and one carrying an integer.
  ^bb1:
    "llvm.br"()[^bb2] <{loop_annotation = #llvm.loop_annotation<unroll = <runtimeDisable = true>, mustProgress = true, isVectorized = true>}> : () -> ()
  ^bb2:
    "llvm.br"()[^bb3] <{loop_annotation = #llvm.loop_annotation<peeled = <count = 2 : i32>, mustProgress = true>}> : () -> ()
  ^bb3:
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "loop_annotation" = #llvm.loop_annotation<mustProgress = true>
// CHECK: "loop_annotation" = #llvm.loop_annotation<unroll = <runtimeDisable = true>, mustProgress = true, isVectorized = true>
// CHECK: "loop_annotation" = #llvm.loop_annotation<peeled = <count = 2 : i32>, mustProgress = true>
