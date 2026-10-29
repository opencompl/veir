// RUN: veir-opt %s --print-op-generic -p=llvm-to-gmir,legalize-riscv64 > %t
// RUN: filecheck %s --check-prefix=LEGAL < %t
// RUN: veir-opt %t --print-op-generic -p=legalize-riscv64,postlegalizer-combiner-riscv64 | filecheck %s --check-prefix=LEGAL
// RUN: veir-opt %t --print-op-generic -p=isel-riscv64,reconcile-cast,riscv-combine,dce | filecheck %s --check-prefix=ISEL

// Legalization keeps word operations and their flags until instruction selection.
"builtin.module"() ({
  "func.func"() <{sym_name = "add", function_type = (i32, i32) -> i32}> ({
  ^bb(%a: i32, %b: i32):
    %r = "llvm.add"(%a, %b) <{overflowFlags = 3 : i32}> : (i32, i32) -> i32
    // LEGAL: "gmir.g_addw"({{.*}}) <{"overflowFlags" = 3 : i32}> : (i64, i64) -> i64
    // ISEL: "riscv.addw"({{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
  "func.func"() <{sym_name = "sub", function_type = (i32, i32) -> i32}> ({
  ^bb(%a: i32, %b: i32):
    %r = "llvm.sub"(%a, %b) <{overflowFlags = 3 : i32}> : (i32, i32) -> i32
    // LEGAL: "gmir.g_subw"({{.*}}) <{"overflowFlags" = 3 : i32}> : (i64, i64) -> i64
    // ISEL: "riscv.subw"({{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
  "func.func"() <{sym_name = "mul", function_type = (i32, i32) -> i32}> ({
  ^bb(%a: i32, %b: i32):
    %r = "llvm.mul"(%a, %b) <{overflowFlags = 3 : i32}> : (i32, i32) -> i32
    // LEGAL: "gmir.g_mulw"({{.*}}) <{"overflowFlags" = 3 : i32}> : (i64, i64) -> i64
    // ISEL: "riscv.mulw"({{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
  "func.func"() <{sym_name = "sdiv", function_type = (i32, i32) -> i32}> ({
  ^bb(%a: i32, %b: i32):
    %r = "llvm.sdiv"(%a, %b) <{isExact}> : (i32, i32) -> i32
    // LEGAL: "gmir.g_sdivw"({{.*}}) <{isExact}> : (i64, i64) -> i64
    // ISEL: "riscv.divw"({{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
  "func.func"() <{sym_name = "udiv", function_type = (i32, i32) -> i32}> ({
  ^bb(%a: i32, %b: i32):
    %r = "llvm.udiv"(%a, %b) <{isExact}> : (i32, i32) -> i32
    // LEGAL: "gmir.g_udivw"({{.*}}) <{isExact}> : (i64, i64) -> i64
    // ISEL: "riscv.divuw"({{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
  "func.func"() <{sym_name = "urem", function_type = (i32, i32) -> i32}> ({
  ^bb(%a: i32, %b: i32):
    %r = "llvm.urem"(%a, %b) : (i32, i32) -> i32
    // LEGAL: "gmir.g_uremw"({{.*}}) : (i64, i64) -> i64
    // ISEL: "riscv.remuw"({{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
  "func.func"() <{sym_name = "shl", function_type = (i32, i32) -> i32}> ({
  ^bb(%a: i32, %b: i32):
    %r = "llvm.shl"(%a, %b) <{overflowFlags = 3 : i32}> : (i32, i32) -> i32
    // LEGAL: "gmir.g_shlw"({{.*}}) <{"overflowFlags" = 3 : i32}> : (i64, i64) -> i64
    // ISEL: "riscv.sllw"({{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
  "func.func"() <{sym_name = "lshr", function_type = (i32, i32) -> i32}> ({
  ^bb(%a: i32, %b: i32):
    %r = "llvm.lshr"(%a, %b) <{isExact}> : (i32, i32) -> i32
    // LEGAL: "gmir.g_lshrw"({{.*}}) <{isExact}> : (i64, i64) -> i64
    // ISEL: "riscv.srlw"({{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
  "func.func"() <{sym_name = "ashr", function_type = (i32, i32) -> i32}> ({
  ^bb(%a: i32, %b: i32):
    %r = "llvm.ashr"(%a, %b) <{isExact}> : (i32, i32) -> i32
    // LEGAL: "gmir.g_ashrw"({{.*}}) <{isExact}> : (i64, i64) -> i64
    // ISEL: "riscv.sraw"({{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
