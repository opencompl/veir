// RUN: veir-interpret %s | filecheck %s
// RUN: LLUBI

// A load through `llvm.inttoptr` of 0 is a load from null, which is
// undefined behaviour.
// TODO: Alive2 (alive-exec) returns poison here instead: it makes an
// out-of-bounds read poison and only an out-of-bounds write UB, while the
// interpreter makes any failed access undefined behaviour.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %q = "llvm.inttoptr"(%zero) : (i64) -> !llvm.ptr
    %v = "llvm.load"(%q) : (!llvm.ptr) -> i64
    "llvm.return"(%v) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
