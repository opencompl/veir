// RUN: veir-interpret %s | filecheck %s --check-prefix=EXEC
// RUN: veir-opt %s -p=isel-br-riscv64 > %t
// RUN: veir-interpret %t | filecheck %s --check-prefix=EXEC
// RUN: filecheck %s --input-file=%t

// A pointer passed along a branch travels as its address in a register, and
// comes back in the successor as the wild pointer at that address. Each access
// through it finds the object again: the store lands in the second object, not
// in the first, and the load reads it back.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %first = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %second = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    "llvm.store"(%zero, %first) : (i64, !llvm.ptr) -> ()
    // CHECK: %[[REG:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.ptr) -> !riscv.reg
    // CHECK: "riscv_cf.branch"(%[[REG]])
    "llvm.br"(%second) [^bb1] : (!llvm.ptr) -> ()
  ^bb1(%p : !llvm.ptr):
    // CHECK: ^{{.*}}(%[[ARG:.*]] : !riscv.reg):
    // CHECK: "builtin.unrealized_conversion_cast"(%[[ARG]]) : (!riscv.reg) -> !llvm.ptr
    %value = "llvm.mlir.constant"() <{value = 42 : i64}> : () -> i64
    "llvm.store"(%value, %p) : (i64, !llvm.ptr) -> ()
    %a = "llvm.load"(%first) : (!llvm.ptr) -> i64
    %b = "llvm.load"(%p) : (!llvm.ptr) -> i64
    %sum = "llvm.add"(%a, %b) : (i64, i64) -> i64
    "llvm.return"(%sum) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// EXEC: Program output: #[0x000000000000002a#64]
