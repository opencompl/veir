; End-to-end: LLVM IR using the intrinsics the Veir LLVM dialect supports,
; lowered all the way to RISC-V via isel-riscv64.
;
;   smax/smin/umax/umin  -> max/min/maxu/minu   (Zbb)
;   fshl/fshr (rotate form, identical data ops) -> rol/ror   (Zbb)
;   fshl/fshr (rotate form, constant amount)    -> rori      (Zbb)
;   ctlz/cttz/ctpop      -> clz/ctz/cpop         (Zbb)
;   bswap                -> rev8                  (Zbb)
;   bitreverse           -> SWAR stages + rev8    (Zbb)
;
; Import the IR to the MLIR LLVM dialect with mlir-translate, lower to generic
; form with mlir-opt, then run the RISC-V instruction selector with veir-opt.

; REQUIRES: mlir-translate, mlir-opt
; RUN: mlir-translate --import-llvm %s | mlir-opt --mlir-print-op-generic --mlir-print-local-scope | veir-opt -p=isel-riscv64 | filecheck %s

declare i64 @llvm.fshl.i64(i64, i64, i64)
declare i64 @llvm.fshr.i64(i64, i64, i64)
declare i64 @llvm.smax.i64(i64, i64)
declare i64 @llvm.smin.i64(i64, i64)
declare i64 @llvm.umax.i64(i64, i64)
declare i64 @llvm.umin.i64(i64, i64)
declare i64 @llvm.ctlz.i64(i64, i1)
declare i64 @llvm.cttz.i64(i64, i1)
declare i64 @llvm.ctpop.i64(i64)
declare i64 @llvm.bswap.i64(i64)
declare i64 @llvm.bitreverse.i64(i64)

; CHECK-LABEL: "sym_name" = "test_rotl"
; CHECK: "riscv.rol"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
define i64 @test_rotl(i64 %a, i64 %s) {
  %r = call i64 @llvm.fshl.i64(i64 %a, i64 %a, i64 %s)
  ret i64 %r
}

; CHECK-LABEL: "sym_name" = "test_rotr"
; CHECK: "riscv.ror"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
define i64 @test_rotr(i64 %a, i64 %s) {
  %r = call i64 @llvm.fshr.i64(i64 %a, i64 %a, i64 %s)
  ret i64 %r
}

; CHECK-LABEL: "sym_name" = "test_rotl_const"
; CHECK: "riscv.rori"(%{{.*}}) <{"value" = 59 : i64}> : (!riscv.reg) -> !riscv.reg
define i64 @test_rotl_const(i64 %a) {
  %r = call i64 @llvm.fshl.i64(i64 %a, i64 %a, i64 5)
  ret i64 %r
}

; CHECK-LABEL: "sym_name" = "test_rotr_const"
; CHECK: "riscv.rori"(%{{.*}}) <{"value" = 5 : i64}> : (!riscv.reg) -> !riscv.reg
define i64 @test_rotr_const(i64 %a) {
  %r = call i64 @llvm.fshr.i64(i64 %a, i64 %a, i64 5)
  ret i64 %r
}

; CHECK-LABEL: "sym_name" = "test_smax"
; CHECK: "riscv.max"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
define i64 @test_smax(i64 %a, i64 %b) {
  %r = call i64 @llvm.smax.i64(i64 %a, i64 %b)
  ret i64 %r
}

; CHECK-LABEL: "sym_name" = "test_smin"
; CHECK: "riscv.min"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
define i64 @test_smin(i64 %a, i64 %b) {
  %r = call i64 @llvm.smin.i64(i64 %a, i64 %b)
  ret i64 %r
}

; CHECK-LABEL: "sym_name" = "test_umax"
; CHECK: "riscv.maxu"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
define i64 @test_umax(i64 %a, i64 %b) {
  %r = call i64 @llvm.umax.i64(i64 %a, i64 %b)
  ret i64 %r
}

; CHECK-LABEL: "sym_name" = "test_umin"
; CHECK: "riscv.minu"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
define i64 @test_umin(i64 %a, i64 %b) {
  %r = call i64 @llvm.umin.i64(i64 %a, i64 %b)
  ret i64 %r
}

; CHECK-LABEL: "sym_name" = "test_ctlz"
; CHECK: "riscv.clz"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
define i64 @test_ctlz(i64 %a) {
  %r = call i64 @llvm.ctlz.i64(i64 %a, i1 false)
  ret i64 %r
}

; CHECK-LABEL: "sym_name" = "test_cttz"
; CHECK: "riscv.ctz"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
define i64 @test_cttz(i64 %a) {
  %r = call i64 @llvm.cttz.i64(i64 %a, i1 false)
  ret i64 %r
}

; CHECK-LABEL: "sym_name" = "test_ctpop"
; CHECK: "riscv.cpop"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
define i64 @test_ctpop(i64 %a) {
  %r = call i64 @llvm.ctpop.i64(i64 %a)
  ret i64 %r
}

; CHECK-LABEL: "sym_name" = "test_bswap"
; CHECK: "riscv.rev8"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
define i64 @test_bswap(i64 %a) {
  %r = call i64 @llvm.bswap.i64(i64 %a)
  ret i64 %r
}

; CHECK-LABEL: "sym_name" = "test_bitreverse"
; CHECK: "riscv.and"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
; CHECK: "riscv.slli"(%{{.*}}) <{{.*}}> : (!riscv.reg) -> !riscv.reg
; CHECK: "riscv.srli"(%{{.*}}) <{{.*}}> : (!riscv.reg) -> !riscv.reg
; CHECK: "riscv.or"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
; CHECK: "riscv.rev8"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
define i64 @test_bitreverse(i64 %a) {
  %r = call i64 @llvm.bitreverse.i64(i64 %a)
  ret i64 %r
}
