// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP
//
// `#llvm.memory_effects` is what `llvm.func` and `llvm.call` carry in place of
// LLVM's `memory(...)` attribute:

"builtin.module"() ({
  // Reads through its pointer arguments and nothing else.
  "llvm.func"() <{function_type = !llvm.func<i32 (!llvm.ptr)>, linkage = #llvm.linkage<external>, sym_name = "reader", memory_effects = #llvm.memory_effects<other = none, argMem = read, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>}> ({
  ^bb0(%p: !llvm.ptr):
    %v = "llvm.load"(%p) <{alignment = 4 : i64}> : (!llvm.ptr) -> i32
    "llvm.return"(%v) : (i32) -> ()
  }) : () -> ()
  // Touches nothing at all: the `memory(none)` of a pure function.
  "llvm.func"() <{function_type = !llvm.func<i32 (i32)>, linkage = #llvm.linkage<external>, sym_name = "pure", memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>}> ({
  ^bb0(%x: i32):
    "llvm.return"(%x) : (i32) -> ()
  }) : () -> ()
  // Unconstrained, and the effect rides on the call site too.
  "llvm.func"() <{function_type = !llvm.func<void (!llvm.ptr)>, linkage = #llvm.linkage<external>, sym_name = "caller", memory_effects = #llvm.memory_effects<other = readwrite, argMem = readwrite, inaccessibleMem = none, errnoMem = readwrite, targetMem0 = none, targetMem1 = none>}> ({
  ^bb0(%p: !llvm.ptr):
    %v = "llvm.call"(%p) <{callee = @reader, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, memory_effects = #llvm.memory_effects<other = none, argMem = read, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>}> : (!llvm.ptr) -> i32
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "memory_effects" = #llvm.memory_effects<other = none, argMem = read, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>
// CHECK: "memory_effects" = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>
// CHECK: "memory_effects" = #llvm.memory_effects<other = readwrite, argMem = readwrite, inaccessibleMem = none, errnoMem = readwrite, targetMem0 = none, targetMem1 = none>
// CHECK: "memory_effects" = #llvm.memory_effects<other = none, argMem = read, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>
