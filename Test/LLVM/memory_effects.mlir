// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP
//
// `#llvm.memory_effects<...>` records which classes of memory a function may
// read or write. It reaches VeIR as the `memory_effects` attribute of
// `llvm.func` and `llvm.call`.
//
// Both cases below spell out all six fields, because that is what `mlir-opt`
// requires: it rejects a shorter field list outright. VeIR keeps the body
// verbatim and so accepts any field set, which is the point -- `errnoMem` and
// `targetMem0`/`targetMem1` are recent additions and the list will grow again.
// UnitTest/AttrParser.lean pins a short form that only VeIR accepts.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<i32 (!llvm.ptr)>, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = none, argMem = read, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, sym_name = "reads_args"}> ({
  ^bb0(%p: !llvm.ptr):
    %c = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    "llvm.return"(%c) : (i32) -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<void ()>, linkage = #llvm.linkage<external>, memory_effects = #llvm.memory_effects<other = readwrite, argMem = readwrite, inaccessibleMem = none, errnoMem = readwrite, targetMem0 = none, targetMem1 = none>, sym_name = "everything"}> ({
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "memory_effects" = #llvm.memory_effects<other = none, argMem = read, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>
// CHECK: "memory_effects" = #llvm.memory_effects<other = readwrite, argMem = readwrite, inaccessibleMem = none, errnoMem = readwrite, targetMem0 = none, targetMem1 = none>
