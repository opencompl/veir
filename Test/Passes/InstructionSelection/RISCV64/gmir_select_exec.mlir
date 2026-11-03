// RUN: veir-opt %s --print-op-generic -p=riscv | veir-interpret | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i8, i8)}> ({
    %a64 = "llvm.mlir.constant"() <{value = 0x1122334455667788 : i64}> : () -> i64
    %b64 = "llvm.mlir.constant"() <{value = -2 : i64}> : () -> i64
    %a8 = "llvm.mlir.constant"() <{value = 0x5a : i8}> : () -> i8
    %b8 = "llvm.mlir.constant"() <{value = 0x7f : i8}> : () -> i8
    %zero8 = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    // A condition truncated from a value with other bits set: only its lowest bit counts.
    %two = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %trunc_false = "llvm.trunc"(%two) <{overflowFlags = 0 : i32}> : (i64) -> i1
    %lt = "llvm.icmp"(%b64, %a64) <{predicate = 2 : i64}> : (i64, i64) -> i1
    %r0 = "llvm.select"(%lt, %a64, %b64) : (i1, i64, i64) -> i64
    %r1 = "llvm.select"(%trunc_false, %a8, %b8) : (i1, i8, i8) -> i8
    %r2 = "llvm.select"(%lt, %a8, %zero8) : (i1, i8, i8) -> i8
    "func.return"(%r0, %r1, %r2) : (i64, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x1122334455667788#64, 0x7f#8, 0x5a#8]
