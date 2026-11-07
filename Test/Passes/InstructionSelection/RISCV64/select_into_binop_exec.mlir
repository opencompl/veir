// RUN: veir-interpret %s | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=riscv | veir-interpret | filecheck %s

// Functional check for `select_into_binop_pattern`: each operation, on both arms, on a true and on
// a false condition. The last two results keep the operation alive with another use.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32)}> ({
    %a = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %b = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %ct = "llvm.icmp"(%a, %b) <{predicate = 6 : i64}> : (i64, i64) -> i1
    %cf = "llvm.icmp"(%b, %a) <{predicate = 6 : i64}> : (i64, i64) -> i1
    %x = "llvm.mlir.constant"() <{value = -1412567295 : i32}> : () -> i32
    %k0 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %o0 = "llvm.shl"(%x, %k0) : (i32, i32) -> i32
    %r0t = "llvm.select"(%ct, %o0, %x) : (i1, i32, i32) -> i32
    %s0t = "llvm.select"(%ct, %x, %o0) : (i1, i32, i32) -> i32
    %r0f = "llvm.select"(%cf, %o0, %x) : (i1, i32, i32) -> i32
    %s0f = "llvm.select"(%cf, %x, %o0) : (i1, i32, i32) -> i32
    %k1 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %o1 = "llvm.lshr"(%x, %k1) : (i32, i32) -> i32
    %r1t = "llvm.select"(%ct, %o1, %x) : (i1, i32, i32) -> i32
    %s1t = "llvm.select"(%ct, %x, %o1) : (i1, i32, i32) -> i32
    %r1f = "llvm.select"(%cf, %o1, %x) : (i1, i32, i32) -> i32
    %s1f = "llvm.select"(%cf, %x, %o1) : (i1, i32, i32) -> i32
    %k2 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %o2 = "llvm.ashr"(%x, %k2) : (i32, i32) -> i32
    %r2t = "llvm.select"(%ct, %o2, %x) : (i1, i32, i32) -> i32
    %s2t = "llvm.select"(%ct, %x, %o2) : (i1, i32, i32) -> i32
    %r2f = "llvm.select"(%cf, %o2, %x) : (i1, i32, i32) -> i32
    %s2f = "llvm.select"(%cf, %x, %o2) : (i1, i32, i32) -> i32
    %k3 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %o3 = "llvm.sub"(%x, %k3) : (i32, i32) -> i32
    %r3t = "llvm.select"(%ct, %o3, %x) : (i1, i32, i32) -> i32
    %s3t = "llvm.select"(%ct, %x, %o3) : (i1, i32, i32) -> i32
    %r3f = "llvm.select"(%cf, %o3, %x) : (i1, i32, i32) -> i32
    %s3f = "llvm.select"(%cf, %x, %o3) : (i1, i32, i32) -> i32
    %k4 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %o4 = "llvm.add"(%x, %k4) : (i32, i32) -> i32
    %r4t = "llvm.select"(%ct, %o4, %x) : (i1, i32, i32) -> i32
    %s4t = "llvm.select"(%ct, %x, %o4) : (i1, i32, i32) -> i32
    %r4f = "llvm.select"(%cf, %o4, %x) : (i1, i32, i32) -> i32
    %s4f = "llvm.select"(%cf, %x, %o4) : (i1, i32, i32) -> i32
    %k5 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %o5 = "llvm.or"(%x, %k5) : (i32, i32) -> i32
    %r5t = "llvm.select"(%ct, %o5, %x) : (i1, i32, i32) -> i32
    %s5t = "llvm.select"(%ct, %x, %o5) : (i1, i32, i32) -> i32
    %r5f = "llvm.select"(%cf, %o5, %x) : (i1, i32, i32) -> i32
    %s5f = "llvm.select"(%cf, %x, %o5) : (i1, i32, i32) -> i32
    %k6 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %o6 = "llvm.xor"(%x, %k6) : (i32, i32) -> i32
    %r6t = "llvm.select"(%ct, %o6, %x) : (i1, i32, i32) -> i32
    %s6t = "llvm.select"(%ct, %x, %o6) : (i1, i32, i32) -> i32
    %r6f = "llvm.select"(%cf, %o6, %x) : (i1, i32, i32) -> i32
    %s6f = "llvm.select"(%cf, %x, %o6) : (i1, i32, i32) -> i32
    %k7 = "llvm.mlir.constant"() <{value = -1 : i32}> : () -> i32
    %o7 = "llvm.add"(%x, %k7) : (i32, i32) -> i32
    %r7t = "llvm.select"(%ct, %o7, %x) : (i1, i32, i32) -> i32
    %s7t = "llvm.select"(%ct, %x, %o7) : (i1, i32, i32) -> i32
    %r7f = "llvm.select"(%cf, %o7, %x) : (i1, i32, i32) -> i32
    %s7f = "llvm.select"(%cf, %x, %o7) : (i1, i32, i32) -> i32
    %k8 = "llvm.mlir.constant"() <{value = 16 : i32}> : () -> i32
    %o8 = "llvm.add"(%x, %k8) : (i32, i32) -> i32
    %r8t = "llvm.select"(%ct, %o8, %x) : (i1, i32, i32) -> i32
    %s8t = "llvm.select"(%ct, %x, %o8) : (i1, i32, i32) -> i32
    %r8f = "llvm.select"(%cf, %o8, %x) : (i1, i32, i32) -> i32
    %s8f = "llvm.select"(%cf, %x, %o8) : (i1, i32, i32) -> i32
    %k9 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %o9 = "llvm.or"(%x, %k9) : (i32, i32) -> i32
    %r9t = "llvm.select"(%ct, %o9, %x) : (i1, i32, i32) -> i32
    %s9t = "llvm.select"(%ct, %x, %o9) : (i1, i32, i32) -> i32
    %r9f = "llvm.select"(%cf, %o9, %x) : (i1, i32, i32) -> i32
    %s9f = "llvm.select"(%cf, %x, %o9) : (i1, i32, i32) -> i32
    "func.return"(%r0t, %s0t, %r0f, %s0f, %r1t, %s1t, %r1f, %s1f, %r2t, %s2t, %r2f, %s2f, %r3t, %s3t, %r3f, %s3f, %r4t, %s4t, %r4f, %s4f, %r5t, %s5t, %r5f, %s5f, %r6t, %s6t, %r6f, %s6f, %r7t, %s7t, %r7f, %s7f, %r8t, %s8t, %r8f, %s8f, %r9t, %s9t, %r9f, %s9f, %o0, %o4) : (i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x5e6f7808#32, 0xabcdef01#32, 0xabcdef01#32, 0x5e6f7808#32, 0x1579bde0#32, 0xabcdef01#32, 0xabcdef01#32, 0x1579bde0#32, 0xf579bde0#32, 0xabcdef01#32, 0xabcdef01#32, 0xf579bde0#32, 0xabcdeefc#32, 0xabcdef01#32, 0xabcdef01#32, 0xabcdeefc#32, 0xabcdef06#32, 0xabcdef01#32, 0xabcdef01#32, 0xabcdef06#32, 0xabcdef07#32, 0xabcdef01#32, 0xabcdef01#32, 0xabcdef07#32, 0xabcdef07#32, 0xabcdef01#32, 0xabcdef01#32, 0xabcdef07#32, 0xabcdef00#32, 0xabcdef01#32, 0xabcdef01#32, 0xabcdef00#32, 0xabcdef11#32, 0xabcdef01#32, 0xabcdef01#32, 0xabcdef11#32, 0xabcdef01#32, 0xabcdef01#32, 0xabcdef01#32, 0xabcdef01#32, 0x5e6f7808#32, 0xabcdef06#32]
