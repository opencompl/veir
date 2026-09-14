// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  "llvm.comdat"() <{sym_name = "c"}> ({
    "llvm.comdat_selector"() <{comdat = 0 : i64, sym_name = "any"}> : () -> ()
    "llvm.comdat_selector"() <{comdat = 1 : i64, sym_name = "exactmatch"}> : () -> ()
    "llvm.comdat_selector"() <{comdat = 2 : i64, sym_name = "largest"}> : () -> ()
    "llvm.comdat_selector"() <{comdat = 3 : i64, sym_name = "nodeduplicate"}> : () -> ()
    "llvm.comdat_selector"() <{comdat = 4 : i64, sym_name = "samesize"}> : () -> ()
  }) : () -> ()
  "llvm.func"() <{comdat = @c::@any, function_type = !llvm.func<void ()>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  }) : () -> ()
  "llvm.mlir.global"() <{addr_space = 0 : i32, comdat = @c::@largest, global_type = i32, linkage = #llvm.linkage<external>, sym_name = "g", value = 0 : i32}> ({
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.comdat"() <{"sym_name" = "c"}> ({
// CHECK: "llvm.comdat_selector"() <{"comdat" = 0 : i64, "sym_name" = "any"}> : () -> ()
// CHECK: "llvm.comdat_selector"() <{"comdat" = 1 : i64, "sym_name" = "exactmatch"}> : () -> ()
// CHECK: "llvm.comdat_selector"() <{"comdat" = 2 : i64, "sym_name" = "largest"}> : () -> ()
// CHECK: "llvm.comdat_selector"() <{"comdat" = 3 : i64, "sym_name" = "nodeduplicate"}> : () -> ()
// CHECK: "llvm.comdat_selector"() <{"comdat" = 4 : i64, "sym_name" = "samesize"}> : () -> ()
// CHECK: "llvm.func"() <{{{.*}}"comdat" = @c::@any{{.*}}}> ({
// CHECK: "llvm.mlir.global"() <{{{.*}}"comdat" = @c::@largest{{.*}}}> ({
