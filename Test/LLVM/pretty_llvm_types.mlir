// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (!llvm.array<2 x x86_amx>)>, linkage = #llvm.linkage<external>, sym_name = "use_x86_amx"}> ({
  ^bb0(%arg0: !llvm.array<2 x !llvm.x86_amx>):
    "llvm.return"() : () -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<void (!llvm.array<4 x ppc_fp128>)>, linkage = #llvm.linkage<external>, sym_name = "use_ppc_fp128"}> ({
  ^bb0(%arg0: !llvm.array<4 x !llvm.ppc_fp128>):
    "llvm.return"() : () -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<void (!llvm.array<1 x metadata>)>, linkage = #llvm.linkage<external>, sym_name = "use_metadata"}> ({
  ^bb0(%arg0: !llvm.array<1 x !llvm.metadata>):
    "llvm.return"() : () -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<void (!llvm.array<1 x label>)>, linkage = #llvm.linkage<external>, sym_name = "use_label"}> ({
  ^bb0(%arg0: !llvm.array<1 x !llvm.label>):
    "llvm.return"() : () -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<void (!llvm.x86_amx)>, linkage = #llvm.linkage<external>, sym_name = "use_full_prefix"}> ({
  ^bb0(%arg0: !llvm.x86_amx):
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: !llvm.array<2 x !llvm.x86_amx>
// CHECK: !llvm.array<4 x !llvm.ppc_fp128>
// CHECK: !llvm.array<1 x !llvm.metadata>
// CHECK: !llvm.array<1 x !llvm.label>
// CHECK: !llvm.x86_amx
