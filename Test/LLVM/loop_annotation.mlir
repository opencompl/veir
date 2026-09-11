// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP
//
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (i1)>, linkage = #llvm.linkage<external>, sym_name = "loop"}> ({
  ^bb0(%c: i1):
    "llvm.cond_br"(%c)[^bb1, ^bb3] <{loop_annotation = #llvm.loop_annotation<mustProgress = true>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
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
