// RUN: VEIR_ROUNDTRIP

// LLVM function pointers and comdat references survive function lowering.
"builtin.module"() ({
  "llvm.comdat"() <{sym_name = "c"}> ({
    "llvm.comdat_selector"() <{comdat = 0 : i64, sym_name = "any"}> : () -> ()
  }) : () -> ()
  "riscv_cf.func"() <{sym_name = "target", function_type = () -> (), comdat = @c::@any, linkage = #llvm.linkage<linkonce_odr>}> ({
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
  "llvm.func"() <{sym_name = "address", function_type = !llvm.func<ptr ()>}> ({
    %p = "llvm.mlir.addressof"() <{global_name = @target}> : () -> !llvm.ptr
    "llvm.return"(%p) : (!llvm.ptr) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "riscv_cf.func"() <{"comdat" = @c::@any, "function_type" = () -> (), "linkage" = #llvm.linkage<linkonce_odr>, "sym_name" = "target"}> ({
// CHECK: "llvm.mlir.addressof"() <{"global_name" = @target}> : () -> !llvm.ptr
