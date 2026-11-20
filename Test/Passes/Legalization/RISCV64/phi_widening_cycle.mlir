// RUN: veir-interpret %s | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=legalize-riscv64 > %t
// RUN: filecheck %s --check-prefix=WIDE < %t
// RUN: veir-interpret %t | filecheck %s
// RUN: %if ctree %{ veir-interpret --ctree %t | filecheck %s %}

// The first block sends two different values to the same successor. Widening the first
// block rewrites the back edge from the second, whose arguments are widened next.
// On the second trip around the loop the false edge forwards 71.

// WIDE: ^{{.*}}(%{{[^:]*}} : i64, %{{[^:]*}} : i64):
// WIDE: ^{{.*}}(%{{[^:]*}} : i64, %{{[^:]*}} : i64):
// CHECK: Program output: #[0x47#8]

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i8}> ({
  ^entry:
    %initial = "llvm.mlir.constant"() <{value = 29 : i8}> : () -> i8
    %next = "llvm.mlir.constant"() <{value = 71 : i8}> : () -> i8
    %yes = "llvm.mlir.constant"() <{value = true}> : () -> i1
    %no = "llvm.mlir.constant"() <{value = false}> : () -> i1
    "cf.br"(%initial, %yes) [^first] : (i8, i1) -> ()
  ^first(%x : i8, %again : i1):
    "cf.cond_br"(%again, %x, %again, %next, %again) [^second, ^second] <{operandSegmentSizes = array<i32: 1, 2, 2>}> : (i1, i8, i1, i8, i1) -> ()
  ^second(%y : i8, %repeat : i1):
    "cf.cond_br"(%repeat, %y, %no, %y) [^first, ^exit] <{operandSegmentSizes = array<i32: 1, 2, 1>}> : (i1, i8, i1, i8) -> ()
  ^exit(%result : i8):
    "func.return"(%result) : (i8) -> ()
  }) : () -> ()
}) : () -> ()
