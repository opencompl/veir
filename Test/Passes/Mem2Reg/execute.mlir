// RUN: veir-interpret %s | filecheck %s --check-prefix=EXEC
// RUN: veir-interpret --ctree %s | filecheck %s --check-prefix=EXEC
// RUN: veir-opt %s --print-op-generic -p=mem2reg > %t
// RUN: filecheck %s --input-file=%t --check-prefix=IR
// RUN: veir-interpret %t | filecheck %s --check-prefix=EXEC
// RUN: veir-interpret --ctree %t | filecheck %s --check-prefix=EXEC

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i32}> ({
    %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
    %a = "arith.constant"() <{value = 10 : i32}> : () -> i32
    %b = "arith.constant"() <{value = 20 : i32}> : () -> i32
    %p = "llvm.alloca"(%one) <{elem_type = i32}> : (i64) -> !llvm.ptr
    %q = "llvm.alloca"(%one) <{elem_type = i32}> : (i64) -> !llvm.ptr
    "llvm.store"(%a, %p) : (i32, !llvm.ptr) -> ()
    %first = "llvm.load"(%p) : (!llvm.ptr) -> i32
    %sum = "arith.addi"(%first, %b) : (i32, i32) -> i32
    "llvm.store"(%sum, %q) : (i32, !llvm.ptr) -> ()
    %r = "llvm.load"(%q) : (!llvm.ptr) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// EXEC: Program output: #[0x0000001e#32]
// IR-LABEL: "sym_name" = "main"
// IR-NOT: "llvm.alloca"
// IR-NOT: "llvm.load"
// IR-NOT: "llvm.store"
// IR: "func.return"
