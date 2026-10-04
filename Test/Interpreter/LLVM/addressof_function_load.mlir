// RUN: veir-interpret %s | filecheck %s
// RUN: LLUBI

// A function's address cannot be read from: a load through it is UB.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void ()>, sym_name = "f"}> ({
    "llvm.return"() : () -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<i8 ()>, sym_name = "main"}> ({
    %f = "llvm.mlir.addressof"() <{global_name = @f}> : () -> !llvm.ptr
    %r = "llvm.load"(%f) : (!llvm.ptr) -> i8
    "llvm.return"(%r) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
