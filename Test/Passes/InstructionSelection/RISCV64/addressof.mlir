// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// Select ordinary symbols, including quoted names; preserve TLS and extern-weak globals.
"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, global_type = i32, linkage = #llvm.linkage<external>, sym_name = ".regular", value = 0 : i32}> ({
  }) : () -> ()
  "llvm.mlir.global"() <{addr_space = 0 : i32, global_type = i32, linkage = #llvm.linkage<external>, sym_name = "tls", thread_local_, value = 0 : i32}> ({
  }) : () -> ()
  "llvm.mlir.global"() <{addr_space = 0 : i32, global_type = i32, linkage = #llvm.linkage<extern_weak>, sym_name = "weak"}> ({
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<ptr ()>, linkage = #llvm.linkage<external>, sym_name = "ordinary_address"}> ({
    %p = "llvm.mlir.addressof"() <{global_name = @".regular"}> : () -> !llvm.ptr
    "llvm.return"(%p) : (!llvm.ptr) -> ()
  }) : () -> ()
  // CHECK-LABEL: "ordinary_address"
  // CHECK:      %[[R:.*]] = "riscv.la"() <{"symbol" = @".regular"}>
  // CHECK-NEXT: %[[P:.*]] = "builtin.unrealized_conversion_cast"(%[[R]]) : (!riscv.reg) -> !llvm.ptr
  // CHECK-NEXT: "llvm.return"(%[[P]])
  "llvm.func"() <{function_type = !llvm.func<ptr ()>, linkage = #llvm.linkage<external>, sym_name = "tls_address"}> ({
    %p = "llvm.mlir.addressof"() <{global_name = @tls}> : () -> !llvm.ptr
    "llvm.return"(%p) : (!llvm.ptr) -> ()
  }) : () -> ()
  // CHECK-LABEL: "tls_address"
  // CHECK-NOT:   "riscv.la"
  // CHECK:       "llvm.mlir.addressof"() <{"global_name" = @tls}>
  "llvm.func"() <{function_type = !llvm.func<ptr ()>, linkage = #llvm.linkage<external>, sym_name = "weak_address"}> ({
    %p = "llvm.mlir.addressof"() <{global_name = @weak}> : () -> !llvm.ptr
    "llvm.return"(%p) : (!llvm.ptr) -> ()
  }) : () -> ()
  // CHECK-LABEL: "weak_address"
  // CHECK-NOT:   "riscv.la"
  // CHECK:       "llvm.mlir.addressof"() <{"global_name" = @weak}>
}) : () -> ()
