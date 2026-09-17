// RUN: veir-opt %s -p=riscv > %t
// RUN: veir2mir %t | filecheck %s

// A stack cell holding two i64s. The argument is stored into both slots, both
// slots are read back, and the sum is returned. After `-p=riscv` the cell is a
// single 16-byte `riscv_stack.alloca` addressed at offsets 0 and 8, which is
// the shape upstream LLVM produces for the same program: one `stack` object
// folded into the base operand of each access as `%stack.0`.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 (i64)>}> ({
  ^bb0(%x: i64):
    %two = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %cell = "llvm.alloca"(%two) <{elem_type = i64, alignment = 8 : i64}> : (i64) -> !llvm.ptr
    "llvm.store"(%x, %cell) : (i64, !llvm.ptr) -> ()
    %hi = "llvm.getelementptr"(%cell, %one) <{elem_type = i64, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%x, %hi) : (i64, !llvm.ptr) -> ()
    %a = "llvm.load"(%cell) : (!llvm.ptr) -> i64
    %b = "llvm.load"(%hi) : (!llvm.ptr) -> i64
    %sum = "llvm.add"(%a, %b) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    "llvm.return"(%sum) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// The single i64 argument arrives in a0 = x10.
// CHECK:      define i64 @main(i64 %a0)
// CHECK:      name:            main
// CHECK:      liveins:
// CHECK-NEXT:   - { reg: '$x10' }

// One 16-byte, 8-aligned frame object for the two-element cell.
// CHECK:      stack:
// CHECK-NEXT:   - { id: 0, size: 16, alignment: 8 }

// CHECK:      body:
// CHECK:      bb.0:
// CHECK:        liveins: $x10
// CHECK:        [[ARG:%[a-z0-9_]+]]:gpr = COPY $x10
// Both stores and both loads address the frame object directly; the alloca
// never materializes into a vreg of its own.
// CHECK-NEXT:   SD [[ARG]], %stack.0, 0
// CHECK-NEXT:   SD [[ARG]], %stack.0, 8
// CHECK-NEXT:   [[LO:%[a-z0-9_]+]]:gpr = LD %stack.0, 0
// CHECK-NEXT:   [[HI:%[a-z0-9_]+]]:gpr = LD %stack.0, 8
// CHECK-NEXT:   [[SUM:%[a-z0-9_]+]]:gpr = ADD [[LO]], [[HI]]
// CHECK-NEXT:   $x10 = COPY [[SUM]]
// CHECK-NEXT:   PseudoRET implicit $x10
// CHECK-NOT:    UNHANDLED
