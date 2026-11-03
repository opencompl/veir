// RUN: veir-opt %s --print-op-generic -p=riscv | veir-interpret | filecheck %s

// Check sign extension of negative and positive i7 values and i1 true,
// including an i32 result, through the RISC-V pipeline.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i64, i64, i32)}> ({
    %neg = "llvm.mlir.constant"() <{value = 64 : i7}> : () -> i7
    %pos = "llvm.mlir.constant"() <{value = 63 : i7}> : () -> i7
    %true = "llvm.mlir.constant"() <{value = 1 : i1}> : () -> i1
    %a = "llvm.sext"(%neg) : (i7) -> i64
    %b = "llvm.sext"(%pos) : (i7) -> i64
    %c = "llvm.sext"(%true) : (i1) -> i64
    %d = "llvm.sext"(%neg) : (i7) -> i32
    "func.return"(%a, %b, %c, %d) : (i64, i64, i64, i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xffffffffffffffc0#64, 0x000000000000003f#64, 0xffffffffffffffff#64, 0xffffffc0#32]
