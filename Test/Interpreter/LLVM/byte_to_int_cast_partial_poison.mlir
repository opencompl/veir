// RUN: veir-interpret %s | filecheck %s
// RUN: CTREE
// NO_CROSS_CHECK: a cast of the `llvm.byte` type, which is not LLVM.

// When casting a byte whose upper four bits are poison to integer we keep
// the bits that are not poison and use a ctree effect to choose the poison bits.
// The default choice for these bits is zero.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i8 ()>}> ({
    %poison = "llvm.mlir.poison"() : () -> i8
    %four = "llvm.mlir.constant"() <{value = 4 : i8}> : () -> i8
    %b = "llvm.bitcast"(%poison) : (i8) -> !llvm.byte<8>
    %s = "llvm.shl"(%b, %four) : (!llvm.byte<8>, i8) -> !llvm.byte<8>
    %i = "builtin.unrealized_conversion_cast"(%s) : (!llvm.byte<8>) -> i8
    "llvm.return"(%i) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00#8]
