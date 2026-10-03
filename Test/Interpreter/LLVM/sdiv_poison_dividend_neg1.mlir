// RUN: veir-interpret %s | filecheck %s
// RUN: LLUBI

// `sdiv poison, -1` (width > 1) is immediate UB: the poison dividend could
// refine to intMin, in which case the overflow case applies.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i32 ()>}> ({
    %neg1 = "llvm.mlir.constant"() <{ "value" = -1 : i32 }> : () -> i32
    %one  = "llvm.mlir.constant"() <{ "value" = 1 : i32 }> : () -> i32
    %poison = "llvm.add"(%neg1, %one) <{"overflowFlags" = 2 : i32}> : (i32, i32) -> i32
    %y = "llvm.sdiv"(%poison, %neg1) : (i32, i32) -> i32
    "llvm.return"(%y) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
