// RUN: veir-interpret %s | filecheck %s
// RUN: veir-opt %s -p=simplifycfg > %t && veir-interpret %t | filecheck %s
// RUN: veir-opt %s -p=riscv,simplifycfg > %t && veir-interpret %t | filecheck %s
// RUN: veir-opt %s -p=riscv,canonicalize,simplifycfg > %t && veir-interpret %t | filecheck %s

// All three simplifications fire here: the constant branch is folded, the
// taken edge is forwarded through ^swap and ^drop, and the rest is dead.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
  ^entry:
    %cond = "llvm.mlir.constant"() <{value = true}> : () -> i1
    %a = "llvm.mlir.constant"() <{value = 111 : i64}> : () -> i64
    %b = "llvm.mlir.constant"() <{value = 52 : i64}> : () -> i64
    "llvm.cond_br"(%cond, %a, %b, %b, %a) [^swap, ^other] <{operandSegmentSizes = array<i32: 1, 2, 2>}> : (i1, i64, i64, i64, i64) -> ()
  ^swap(%x : i64, %y : i64):
    "llvm.br"(%y, %x) [^drop] : (i64, i64) -> ()
  ^drop(%p : i64, %q : i64):
    "llvm.br"(%p) [^exit] : (i64) -> ()
  ^other(%s : i64, %t : i64):
    %sum = "llvm.add"(%s, %t) : (i64, i64) -> i64
    "llvm.br"(%sum) [^exit] : (i64) -> ()
  ^exit(%r : i64):
    "llvm.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000034#64]
