; End-to-end: a select of pointers, lowered all the way to RISC-V via the riscv pipeline, reads
; the object of the selected arm.

; REQUIRES: mlir-translate, mlir-opt
; RUN: mlir-translate --import-llvm %s | mlir-opt --mlir-print-op-generic --mlir-print-local-scope | veir-opt -p=riscv | filecheck %s
; RUN: mlir-translate --import-llvm %s | mlir-opt --mlir-print-op-generic --mlir-print-local-scope | veir-opt --print-op-generic -p=riscv | veir-interpret | filecheck %s --check-prefix=EXEC

define i32 @main() {
  %1 = alloca i32, i64 1, align 4
  %2 = alloca i32, i64 1, align 4
  store i32 11, ptr %1, align 4
  store i32 22, ptr %2, align 4
  %3 = select i1 true, ptr %1, ptr %2
  %4 = load i32, ptr %3, align 4
  ret i32 %4
}

; CHECK:      [[EQZ:%.*]] = "riscv.czeroeqz"
; CHECK-NEXT: [[NEZ:%.*]] = "riscv.czeronez"
; CHECK-NEXT: [[SEL:%.*]] = "riscv.or"([[EQZ]], [[NEZ]])
; CHECK-NEXT: "riscv.lw"([[SEL]])
; EXEC: Program output: #[0x000000000000000b#64]
