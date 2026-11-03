// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

// `alignment` is optional on `llvm.mlir.global`: an absent alignment means "use
// the target's preferred alignment" and must survive a round trip as absent,
// rather than being rejected or defaulted. `addr_space` is instead a
// default-valued attribute, so an absent one is materialized as `0 : i32`,
// matching what `mlir-opt` does.

"builtin.module"() ({
  "llvm.mlir.global"() <{global_type = i32, linkage = #llvm.linkage<external>, sym_name = "no_align", value = 41 : i32}> ({
  }) : () -> ()
  "llvm.mlir.global"() <{alignment = 4 : i64, global_type = i32, linkage = #llvm.linkage<external>, sym_name = "with_align", value = 42 : i32}> ({
  }) : () -> ()
}) : () -> ()

// CHECK:      "llvm.mlir.global"()
// CHECK-SAME:   "addr_space" = 0 : i32
// CHECK-NOT:    "alignment"
// CHECK-SAME:   "sym_name" = "no_align"
// CHECK:      "llvm.mlir.global"()
// CHECK-SAME:   "addr_space" = 0 : i32
// CHECK-SAME:   "alignment" = 4 : i64
// CHECK-SAME:   "sym_name" = "with_align"
