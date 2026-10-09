// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP
//
// `llvm.load` and `llvm.store` keep their atomic `ordering`: 1 is `unordered`,
// 2 `monotonic`, 4 `acquire`, 5 `release` and 7 `seq_cst`. A load cannot be
// `release` and a store cannot be `acquire`, and neither can be `acq_rel`
// (each is refused by its own test in Test/Verifier). `not_atomic`, 0, is the
// default and is not printed.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (ptr, i32, f64)>, linkage = #llvm.linkage<external>, sym_name = "atomics"}> ({
  ^bb0(%p: !llvm.ptr, %v: i32, %f: f64):
    %0 = "llvm.load"(%p) <{alignment = 4 : i64, ordering = 1 : i64}> : (!llvm.ptr) -> i32
    %1 = "llvm.load"(%p) <{alignment = 4 : i64, ordering = 2 : i64}> : (!llvm.ptr) -> i32
    %2 = "llvm.load"(%p) <{alignment = 8 : i64, ordering = 4 : i64}> : (!llvm.ptr) -> !llvm.ptr
    %3 = "llvm.load"(%p) <{alignment = 8 : i64, ordering = 7 : i64, syncscope = "singlethread"}> : (!llvm.ptr) -> f64
    %4 = "llvm.load"(%p) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    "llvm.store"(%v, %p) <{alignment = 4 : i64, ordering = 1 : i64}> : (i32, !llvm.ptr) -> ()
    "llvm.store"(%v, %p) <{alignment = 4 : i64, ordering = 2 : i64}> : (i32, !llvm.ptr) -> ()
    "llvm.store"(%v, %p) <{alignment = 4 : i64, ordering = 5 : i64}> : (i32, !llvm.ptr) -> ()
    "llvm.store"(%f, %p) <{alignment = 8 : i64, ordering = 7 : i64, syncscope = "singlethread"}> : (f64, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.load"(%{{.*}}) <{"alignment" = 4 : i64, "ordering" = 1 : i64}> : (!llvm.ptr) -> i32
// CHECK: "llvm.load"(%{{.*}}) <{"alignment" = 4 : i64, "ordering" = 2 : i64}> : (!llvm.ptr) -> i32
// CHECK: "llvm.load"(%{{.*}}) <{"alignment" = 8 : i64, "ordering" = 4 : i64}> : (!llvm.ptr) -> !llvm.ptr
// CHECK: "llvm.load"(%{{.*}}) <{"alignment" = 8 : i64, "ordering" = 7 : i64, "syncscope" = "singlethread"}> : (!llvm.ptr) -> f64
// CHECK: "llvm.load"(%{{.*}}) <{"alignment" = 1 : i64}> : (!llvm.ptr) -> i8
// CHECK: "llvm.store"(%{{.*}}, %{{.*}}) <{"alignment" = 4 : i64, "ordering" = 1 : i64}> : (i32, !llvm.ptr) -> ()
// CHECK: "llvm.store"(%{{.*}}, %{{.*}}) <{"alignment" = 4 : i64, "ordering" = 2 : i64}> : (i32, !llvm.ptr) -> ()
// CHECK: "llvm.store"(%{{.*}}, %{{.*}}) <{"alignment" = 4 : i64, "ordering" = 5 : i64}> : (i32, !llvm.ptr) -> ()
// CHECK: "llvm.store"(%{{.*}}, %{{.*}}) <{"alignment" = 8 : i64, "ordering" = 7 : i64, "syncscope" = "singlethread"}> : (f64, !llvm.ptr) -> ()
