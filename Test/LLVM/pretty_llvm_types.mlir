// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (!llvm.array<2 x x86_amx>)>, linkage = #llvm.linkage<external>, sym_name = "use_x86_amx"}> ({
  ^bb0(%arg0: !llvm.array<2 x !llvm.x86_amx>):
    "llvm.return"() : () -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<void (!llvm.array<4 x ppc_fp128>)>, linkage = #llvm.linkage<external>, sym_name = "use_ppc_fp128"}> ({
  ^bb0(%arg0: !llvm.array<4 x !llvm.ppc_fp128>):
    "llvm.return"() : () -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<void (!llvm.array<1 x target<"spirv.Image", i32, 0, 0, 0, 0, 0, 0>>)>, linkage = #llvm.linkage<external>, sym_name = "use_target"}> ({
  ^bb0(%arg0: !llvm.array<1 x !llvm.target<"spirv.Image", i32, 0, 0, 0, 0, 0, 0>>):
    "llvm.return"() : () -> ()
  }) : () -> ()
  // `metadata` and `label` are invalid as array elements.
  "llvm.func"() <{function_type = !llvm.func<void (metadata, label)>, linkage = #llvm.linkage<external>, sym_name = "use_metadata_and_label"}> ({
  ^bb0(%arg0: !llvm.metadata, %arg1: !llvm.label):
    "llvm.return"() : () -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<void (!llvm.x86_amx, !llvm.target<"aarch64.svcount">)>, linkage = #llvm.linkage<external>, sym_name = "use_full_prefix"}> ({
  ^bb0(%arg0: !llvm.x86_amx, %arg1: !llvm.target<"aarch64.svcount">):
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: !llvm.func<void (!llvm.array<2 x !llvm.x86_amx>)>
// CHECK: (%arg{{[0-9_]+}} : !llvm.array<2 x !llvm.x86_amx>):
// CHECK: !llvm.func<void (!llvm.array<4 x !llvm.ppc_fp128>)>
// CHECK: (%arg{{[0-9_]+}} : !llvm.array<4 x !llvm.ppc_fp128>):
// CHECK: !llvm.func<void (!llvm.array<1 x !llvm.target<"spirv.Image", i32, 0, 0, 0, 0, 0, 0>>)>
// CHECK: (%arg{{[0-9_]+}} : !llvm.array<1 x !llvm.target<"spirv.Image", i32, 0, 0, 0, 0, 0, 0>>):
// CHECK: !llvm.func<void (!llvm.metadata, !llvm.label)>
// CHECK: (%arg{{[0-9_]+}} : !llvm.metadata, %arg{{[0-9_]+}} : !llvm.label):
// CHECK: !llvm.func<void (!llvm.x86_amx, !llvm.target<"aarch64.svcount">)>
// CHECK: (%arg{{[0-9_]+}} : !llvm.x86_amx, %arg{{[0-9_]+}} : !llvm.target<"aarch64.svcount">):
