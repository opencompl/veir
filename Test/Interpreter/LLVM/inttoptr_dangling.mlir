// RUN: veir-interpret %s | filecheck %s
// RUN: LLUBI

// A store through `llvm.inttoptr` of an address that no object covers is
// undefined behaviour: the interpreter runs a closed program, so nothing can
// live at the address.

// ALIVE_EXEC: keeps this store defined: a function open to any calling
// context may find an object placed at the address.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %v = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %addr = "llvm.mlir.constant"() <{value = 69632 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %q = "llvm.inttoptr"(%addr) : (i64) -> !llvm.ptr
    "llvm.store"(%v, %q) : (i64, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
