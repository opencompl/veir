// RUN: VEIR_ROUNDTRIP
//
// A symbol name holding a byte the printer writes as `\n` rather than as hex.
// The escaper and the unescaper have to agree on every escape either uses, or
// VeIR cannot read back the name it just wrote.
//
// There is no MLIR run line: `mlir-opt` writes this name `@"a\0Ab"`, so the
// two printers disagree on the spelling even though both accept either.

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, global_type = i32, linkage = #llvm.linkage<external>, sym_name = "a\nb"}> ({
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<ptr ()>, linkage = #llvm.linkage<external>, sym_name = "get"}> ({
    %p = "llvm.mlir.addressof"() <{global_name = @"a\nb"}> : () -> !llvm.ptr
    "llvm.return"(%p) : (!llvm.ptr) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.mlir.addressof"() <{"global_name" = @"a\nb"}> : () -> !llvm.ptr
