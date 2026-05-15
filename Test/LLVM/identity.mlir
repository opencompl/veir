// RUN: veir-opt %s | filecheck %s

"builtin.module"() ({
  "llvm.module_flags"() : () -> ()
  "llvm.func"() ({
    ^bb0():
      %5 = "llvm.mlir.constant"() <{"value" = 13 : i32}> : () -> i32
      %6 = "llvm.mlir.constant"() <{"value" = 1 : i32}> : () -> i1
      %7 = "llvm.and"(%5, %5) : (i32, i32) -> i32
      %8 = "llvm.or"(%5, %5) : (i32, i32) -> i32
      %9 = "llvm.xor"(%5, %5) : (i32, i32) -> i32
      %add = "llvm.add"(%5, %5) : (i32, i32) -> i32
      %add_nsw = "llvm.add"(%5, %5) <{nsw}> : (i32, i32) -> i32
      %add_nuw = "llvm.add"(%5, %5) <{nuw}> : (i32, i32) -> i32
      %add_nsw_nuw = "llvm.add"(%5, %5) <{nsw, nuw}> : (i32, i32) -> i32
      %11 = "llvm.sub"(%5, %5) : (i32, i32) -> i32
      %mul = "llvm.mul"(%5, %5) : (i32, i32) -> i32
      %mul_nsw = "llvm.mul"(%5, %5) <{nsw}> : (i32, i32) -> i32
      %mul_nuw = "llvm.mul"(%5, %5) <{nuw}> : (i32, i32) -> i32
      %mul_nsw_nuw = "llvm.mul"(%5, %5) <{nsw, nuw}> : (i32, i32) -> i32
      %12 = "llvm.shl"(%5, %5) : (i32, i32) -> i32
      %13 = "llvm.lshr"(%5, %5) : (i32, i32) -> i32
      %14 = "llvm.ashr"(%5, %5) : (i32, i32) -> i32
      %15 = "llvm.sdiv"(%5, %5) : (i32, i32) -> i32
      %16 = "llvm.udiv"(%5, %5) : (i32, i32) -> i32
      %17 = "llvm.urem"(%5, %5) : (i32, i32) -> i32
      %18 = "llvm.srem"(%5, %5) : (i32, i32) -> i32
      %19 = "llvm.icmp"(%5, %5) <{predicate = 0 : i64}> : (i32, i32) -> i1
      %20 = "llvm.select"(%6, %5, %5) : (i1, i32, i32) -> i32
      %21 = "llvm.trunc"(%5) : (i32) -> i1
      %22 = "llvm.sext"(%6) : (i1) -> i32
      %23 = "llvm.zext"(%6) : (i1) -> i32
      %24 = "llvm.alloca"(%5) <{elem_type = i32}> : (i32) -> !llvm.ptr
      %25 = "llvm.alloca"(%5) <{elem_type = i32, alignment = 4 : i32, inalloca}> : (i32) -> !llvm.ptr
      "llvm.store"(%24, %5) : (!llvm.ptr, i32) -> ()
      "llvm.store"(%24, %5) <{alignment = 1 : i32, volatile_, nontemporal, invariantGroup, syncscope = "foo", access_groups = [], alias_scopes = [], noalias_scopes = [], tbaa = []}> : (!llvm.ptr, i32) -> ()
      %26 = "llvm.load"(%24) : (!llvm.ptr) -> i32
      %27 = "llvm.load"(%24) <{alignment = 1 : i32, volatile_, nontemporal, invariant, invariantGroup, syncscope = "foo", access_groups = [], alias_scopes = [], noalias_scopes = [], tbaa = []}> : (!llvm.ptr) -> i32
      "llvm.cond_br"(%6, %5, %5) [^7, ^7] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
    ^7(%arg6_0 : i32):
      "llvm.br"(%arg6_0) [^8] : (i32) -> ()
    ^8(%arg7_0 : i32):
      "llvm.return"(%arg7_0) : (i32) -> ()
    ^9(%ptr : !llvm.ptr):
      %28 = "llvm.getelementptr"(%ptr, %6) <{elem_type = !llvm.struct<(i32, f32)>, noWrapFlags = 3 : i32, rawConstantIndices = array<i32: -2147483648, 0>}> : (!llvm.ptr, i1) -> !llvm.ptr
      %29 = "llvm.getelementptr"(%ptr, %6) <{elem_type = !llvm.struct<(i32, f32)>, noWrapFlags = 2 : i32, rawConstantIndices = array<i32: -2147483648, 0>}> : (!llvm.ptr, i1) -> !llvm.ptr
      %30 = "llvm.getelementptr"(%ptr, %6) <{elem_type = !llvm.struct<(i32, f32)>, noWrapFlags = 1 : i32, rawConstantIndices = array<i32: -2147483648, 0>}> : (!llvm.ptr, i1) -> !llvm.ptr
      %31 = "llvm.getelementptr"(%ptr, %6) <{elem_type = !llvm.struct<(i32, f32)>, noWrapFlags = 0 : i32, rawConstantIndices = array<i32: -2147483648, 0>}> : (!llvm.ptr, i1) -> !llvm.ptr
      %32 = "llvm.getelementptr"(%ptr, %6) <{elem_type = !llvm.struct<(i32, f32)>, rawConstantIndices = array<i32: -2147483648, 0>}> : (!llvm.ptr, i1) -> !llvm.ptr
      "llvm.return"(%28, %29, %30, %31, %32) : (!llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:       "builtin.module"() ({
// CHECK-NEXT:   ^4():
// CHECK-NEXT:     "llvm.module_flags"() : () -> ()
// CHECK-NEXT:     "llvm.func"() ({
// CHECK-NEXT:         ^7():
// CHECK-NEXT:       %{{.*}} = "llvm.mlir.constant"() <{"value" = 13 : i32}> : () -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.mlir.constant"() <{"value" = 1 : i32}> : () -> i1
// CHECK-NEXT:       %{{.*}} = "llvm.and"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.or"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.xor"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.add"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.add"(%{{.*}}, %{{.*}}) <{nsw}> : (i32, i32) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.add"(%{{.*}}, %{{.*}}) <{nuw}> : (i32, i32) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.add"(%{{.*}}, %{{.*}}) <{nsw, nuw}> : (i32, i32) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.sub"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.mul"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.mul"(%{{.*}}, %{{.*}}) <{nsw}> : (i32, i32) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.mul"(%{{.*}}, %{{.*}}) <{nuw}> : (i32, i32) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.mul"(%{{.*}}, %{{.*}}) <{nsw, nuw}> : (i32, i32) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.shl"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.lshr"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.ashr"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.sdiv"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.udiv"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.urem"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.srem"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 0 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:       %{{.*}} = "llvm.select"(%{{.*}}, %{{.*}}, %{{.*}}) : (i1, i32, i32) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.trunc"(%{{.*}}) : (i32) -> i1
// CHECK-NEXT:       %{{.*}} = "llvm.sext"(%{{.*}}) : (i1) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.zext"(%{{.*}}) : (i1) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.alloca"(%{{.*}}) <{"alignment" = 0 : i64, "elem_type" = i32}> : (i32) -> !llvm.ptr
// CHECK-NEXT:       %{{.*}} = "llvm.alloca"(%{{.*}}) <{"alignment" = 4 : i32, "elem_type" = i32, inalloca}> : (i32) -> !llvm.ptr
// CHECK-NEXT:       "llvm.store"(%{{.*}}, %{{.*}}) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 0 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr, i32) -> ()
// CHECK-NEXT:       "llvm.store"(%{{.*}}, %{{.*}}) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i32, invariantGroup, "noalias_scopes" = [], nontemporal, "syncscope" = "foo", "tbaa" = [], volatile_}> : (!llvm.ptr, i32) -> ()
// CHECK-NEXT:       %{{.*}} = "llvm.load"(%{{.*}}) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 0 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.load"(%{{.*}}) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i32, invariant, invariantGroup, "noalias_scopes" = [], nontemporal, "syncscope" = "foo", "tbaa" = [], volatile_}> : (!llvm.ptr) -> i32
// CHECK-NEXT:       "llvm.cond_br"(%{{.*}}, %{{.*}}, %{{.*}}) [^{{.*}}, ^{{.*}}] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
// CHECK-NEXT:     ^{{.*}}(%{{.*}} : i32):
// CHECK-NEXT:       "llvm.br"(%{{.*}}) [^{{.*}}] : (i32) -> ()
// CHECK-NEXT:     ^{{.*}}(%{{.*}} : i32):
// CHECK-NEXT:       "llvm.return"(%{{.*}}) : (i32) -> ()
// CHECK-NEXT:     ^{{.*}}(%{{.*}} : !llvm.ptr):
// CHECK-NEXT:       %{{.*}} = "llvm.getelementptr"(%{{.*}}, %{{.*}}) <{"elem_type" = !llvm.struct<(i32, f32)>, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648, 0>}> : (!llvm.ptr, i1) -> !llvm.ptr
// CHECK-NEXT:       %{{.*}} = "llvm.getelementptr"(%{{.*}}, %{{.*}}) <{"elem_type" = !llvm.struct<(i32, f32)>, "noWrapFlags" = 2 : i32, "rawConstantIndices" = array<i32: -2147483648, 0>}> : (!llvm.ptr, i1) -> !llvm.ptr
// CHECK-NEXT:       %{{.*}} = "llvm.getelementptr"(%{{.*}}, %{{.*}}) <{"elem_type" = !llvm.struct<(i32, f32)>, "noWrapFlags" = 1 : i32, "rawConstantIndices" = array<i32: -2147483648, 0>}> : (!llvm.ptr, i1) -> !llvm.pt
// CHECK-NEXT:       %{{.*}} = "llvm.getelementptr"(%{{.*}}, %{{.*}}) <{"elem_type" = !llvm.struct<(i32, f32)>, "noWrapFlags" = 0 : i32, "rawConstantIndices" = array<i32: -2147483648, 0>}> : (!llvm.ptr, i1) -> !llvm.ptr
// CHECK-NEXT:       %{{.*}} = "llvm.getelementptr"(%{{.*}}, %{{.*}}) <{"elem_type" = !llvm.struct<(i32, f32)>, "noWrapFlags" = 0 : i32, "rawConstantIndices" = array<i32: -2147483648, 0>}> : (!llvm.ptr, i1) -> !llvm.ptr
// CHECK-NEXT:       "llvm.return"(%{{.*}}, %{{.*}}, %{{.*}}, %{{.*}}, %{{.*}}) : (!llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
// CHECK-NEXT:   }) : () -> ()
// CHECK-NEXT: }) : () -> ()
