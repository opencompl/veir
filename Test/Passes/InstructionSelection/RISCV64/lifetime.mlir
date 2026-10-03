// RUN: veir-opt %s -p=isel-riscv64 > %t.partial
// RUN: filecheck %s --input-file=%t.partial --check-prefix=ABSENT
// RUN: veir-interpret %t.partial | filecheck %s --check-prefix=EXEC
// RUN: veir-opt %s -p=riscv > %t
// RUN: filecheck %s --input-file=%t --check-prefix=ABSENT
// RUN: veir-interpret %t | filecheck %s --check-prefix=EXEC
// RUN: veir2mir %t | filecheck %s --check-prefix=MIR

// ABSENT: "builtin.module"
// ABSENT-NOT: llvm.intr.lifetime
// ABSENT-NOT: llvm.mlir.poison
// ABSENT-NOT: llvm.alloca

// Repeated markers, a restart in another block, and an end without a start
// need no runtime instructions. The restarted object keeps the same stack slot,
// and a second object stays intact across the restart.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %eleven = "llvm.mlir.constant"() <{value = 11 : i64}> : () -> i64
    %thirty_one = "llvm.mlir.constant"() <{value = 31 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i64, alignment = 8 : i64}> : (i64) -> !llvm.ptr
    %q = "llvm.alloca"(%one) <{elem_type = i64, alignment = 8 : i64}> : (i64) -> !llvm.ptr
    %poison = "llvm.mlir.poison"() : () -> !llvm.ptr
    "llvm.intr.lifetime.start"(%poison) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%poison) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%p) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%p) : (!llvm.ptr) -> ()
    "llvm.store"(%eleven, %p) : (i64, !llvm.ptr) -> ()
    %first = "llvm.load"(%p) : (!llvm.ptr) -> i64
    "llvm.intr.lifetime.end"(%p) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%p) : (!llvm.ptr) -> ()
    "llvm.store"(%first, %q) : (i64, !llvm.ptr) -> ()
    "llvm.br"()[^restart] : () -> ()
  ^restart:
    "llvm.intr.lifetime.start"(%p) : (!llvm.ptr) -> ()
    "llvm.store"(%thirty_one, %p) : (i64, !llvm.ptr) -> ()
    %second = "llvm.load"(%p) : (!llvm.ptr) -> i64
    %saved = "llvm.load"(%q) : (!llvm.ptr) -> i64
    "llvm.intr.lifetime.end"(%p) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%q) : (!llvm.ptr) -> ()
    %sum = "llvm.add"(%saved, %second) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    "llvm.return"(%sum) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// EXEC: Program output: #[0x000000000000002a#64]

// MIR: name:            main
// MIR: stack:
// MIR-NEXT: - { id: 0, size: 8, alignment: 8 }
// MIR-NEXT: - { id: 1, size: 8, alignment: 8 }
// MIR-NEXT: body:
// MIR: SD {{%[a-z0-9_]+}}, %stack.0, 0
// MIR-NEXT: [[FIRST:%[a-z0-9_]+]]:gpr = LD %stack.0, 0
// MIR-NEXT: SD [[FIRST]], %stack.1, 0
// MIR-NEXT: PseudoBR %bb.1
// MIR: bb.1:
// MIR-NEXT: SD {{%[a-z0-9_]+}}, %stack.0, 0
// MIR-NEXT: [[SECOND:%[a-z0-9_]+]]:gpr = LD %stack.0, 0
// MIR-NEXT: [[SAVED:%[a-z0-9_]+]]:gpr = LD %stack.1, 0
// MIR-NEXT: [[SUM:%[a-z0-9_]+]]:gpr = ADD [[SAVED]], [[SECOND]]
// MIR-NEXT: $x10 = COPY [[SUM]]
// MIR-NEXT: PseudoRET implicit $x10
