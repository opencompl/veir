// RUN: veir-interpret %s | filecheck %s
// RUN: LLUBI
// RUN: ALIVE_EXEC

// Overwriting one byte of a stored pointer leaves bytes that no longer name
// the object. The low byte is the one overwritten: object addresses are
// 16-byte aligned, so forcing it to 1 moves the address off every object
// start, and the load through the reloaded pointer is undefined behaviour.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %one8 = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    %a = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %b = "llvm.alloca"(%one) <{elem_type = !llvm.ptr}> : (i64) -> !llvm.ptr
    "llvm.store"(%a, %b) : (!llvm.ptr, !llvm.ptr) -> ()
    "llvm.store"(%one8, %b) : (i8, !llvm.ptr) -> ()
    %p = "llvm.load"(%b) : (!llvm.ptr) -> !llvm.ptr
    %r = "llvm.load"(%p) : (!llvm.ptr) -> i64
    "llvm.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
