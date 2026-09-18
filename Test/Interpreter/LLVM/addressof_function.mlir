// RUN: veir-interpret %s | filecheck %s

// Functions get objects of their own, so their addresses are distinct from
// every other object's and from null. The addresses themselves are chosen by
// the interpreter, so the test compares two of them rather than naming one.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void ()>, sym_name = "f"}> ({
    "llvm.return"() : () -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<void ()>, sym_name = "g"}> ({
    "llvm.return"() : () -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<i64 ()>, sym_name = "main"}> ({
    %f = "llvm.mlir.addressof"() <{global_name = @f}> : () -> !llvm.ptr
    %g = "llvm.mlir.addressof"() <{global_name = @g}> : () -> !llvm.ptr
    %fi = "llvm.ptrtoint"(%f) : (!llvm.ptr) -> i64
    %gi = "llvm.ptrtoint"(%g) : (!llvm.ptr) -> i64
    %same = "llvm.icmp"(%fi, %gi) <{predicate = 0 : i64}> : (i64, i64) -> i1
    %wide = "llvm.zext"(%same) : (i1) -> i64
    "llvm.return"(%wide) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000000#64]
