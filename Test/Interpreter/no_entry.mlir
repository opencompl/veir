// RUN: veir-interpret %s 2>&1 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, function_type = !llvm.func<i16 ()>, linkage = #llvm.linkage<external>, sym_name = "myfunc", unnamed_addr = 0 : i64, visibility_ = 0 : i64}> ({
    %0 = "llvm.mlir.constant"() <{value = 20 : i16}> : () -> i16
    %1 = "llvm.mlir.constant"() <{value = 13 : i16}> : () -> i16
    %2 = "llvm.add"(%0, %1) <{overflowFlags = 0 : i32}> : (i16, i16) -> i16
    "llvm.return"(%2) : (i16) -> ()
  }) : () -> ()
}) {dlti.dl_spec = #dlti.dl_spec<!llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, i64 = dense<[32, 64]> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little">, llvm.module_asm = [], llvm.target_triple = ""} : () -> ()

// CHECK: Error: No entry point: define a function named 'main' or use top-level executable ops
