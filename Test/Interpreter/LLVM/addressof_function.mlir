// RUN: veir-interpret %s | filecheck %s

// Functions get objects of their own, so their addresses are distinct and
// non-null. `@f` is the first top-level op, so it lands at 0x10000, right
// past the machine arena.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void ()>, sym_name = "f"}> ({
    "llvm.return"() : () -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<i64 ()>, sym_name = "main"}> ({
    %f = "llvm.mlir.addressof"() <{global_name = @f}> : () -> !llvm.ptr
    %a = "llvm.ptrtoint"(%f) : (!llvm.ptr) -> i64
    "llvm.return"(%a) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000010000#64]
