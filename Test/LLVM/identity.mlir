// RUN: VEIR_UNREGISTERED_ROUNDTRIP
// RUN: MLIR_UNREGISTERED_ROUNDTRIP

"builtin.module"() ({
  "llvm.module_flags"() <{flags = [#llvm.mlir.module_flag<error, "wchar_size", 4 : i32>, #llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<max, "PIE Level", 2 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>, #llvm.mlir.module_flag<max, "frame-pointer", 2 : i32>]}> : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, function_type = !llvm.func<i32 (f64)>, linkage = #llvm.linkage<external>, sym_name = "myfunc", unnamed_addr = 0 : i64, visibility_ = 0 : i64}> ({
    ^bb0(%fcst : f64):
      %5 = "llvm.mlir.constant"() <{"value" = 13 : i32}> : () -> i32
      %6 = "llvm.mlir.constant"() <{"value" = 1 : i32}> : () -> i1
      %7 = "llvm.and"(%5, %5) : (i32, i32) -> i32
      %8 = "llvm.or"(%5, %5) : (i32, i32) -> i32
      %9 = "llvm.xor"(%5, %5) : (i32, i32) -> i32
      %smax = "llvm.intr.smax"(%5, %5) : (i32, i32) -> i32
      %smin = "llvm.intr.smin"(%5, %5) : (i32, i32) -> i32
      %umax = "llvm.intr.umax"(%5, %5) : (i32, i32) -> i32
      %umin = "llvm.intr.umin"(%5, %5) : (i32, i32) -> i32
      %add = "llvm.add"(%5, %5) : (i32, i32) -> i32
      %add_nsw = "llvm.add"(%5, %5) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
      %add_nuw = "llvm.add"(%5, %5) <{"overflowFlags" = 2 : i32}> : (i32, i32) -> i32
      %add_nsw_nuw = "llvm.add"(%5, %5) <{"overflowFlags" = 3 : i32}> : (i32, i32) -> i32
      %11 = "llvm.sub"(%5, %5) : (i32, i32) -> i32
      %mul = "llvm.mul"(%5, %5) : (i32, i32) -> i32
      %mul_nsw = "llvm.mul"(%5, %5) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
      %mul_nuw = "llvm.mul"(%5, %5) <{"overflowFlags" = 2 : i32}> : (i32, i32) -> i32
      %mul_nsw_nuw = "llvm.mul"(%5, %5) <{"overflowFlags" = 3 : i32}> : (i32, i32) -> i32
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
      %25 = "llvm.alloca"(%5) <{elem_type = i32, alignment = 4 : i64, inalloca}> : (i32) -> !llvm.ptr
      "llvm.store"(%5, %24) : (i32, !llvm.ptr) -> ()
      "llvm.store"(%5, %24) <{alignment = 1 : i64, volatile_, nontemporal, invariantGroup, access_groups = [], alias_scopes = [], noalias_scopes = [], tbaa = []}> : (i32, !llvm.ptr) -> ()
      %26 = "llvm.load"(%24) : (!llvm.ptr) -> i32
      %27 = "llvm.load"(%24) <{alignment = 1 : i64, volatile_, nontemporal, invariant, invariantGroup, access_groups = [], alias_scopes = [], noalias_scopes = [], tbaa = []}> : (!llvm.ptr) -> i32
      "llvm.cond_br"(%6, %5, %5) [^7, ^7] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
    ^7(%arg6_0 : i32):
      "llvm.br"(%arg6_0) [^8] : (i32) -> ()
    ^8(%arg7_0 : i32):
      "llvm.return"(%arg7_0) : (i32) -> ()
    ^9(%ptr : !llvm.ptr):
      %32 = "llvm.getelementptr"(%ptr, %6) <{elem_type = !llvm.struct<(i32, f32)>, rawConstantIndices = array<i32: -2147483648, 0>}> : (!llvm.ptr, i1) -> !llvm.ptr
      %34 = "llvm.fadd"(%fcst, %fcst) : (f64, f64) -> f64
      %35 = "llvm.fadd"(%fcst, %fcst) <{fastmathFlags = #llvm.fastmath<none, fast>}> : (f64, f64) -> f64
      %36 = "llvm.fadd"(%fcst, %fcst) <{fastmathFlags = #llvm.fastmath<nnan>}> : (f64, f64) -> f64
      %37 = "llvm.fadd"(%fcst, %fcst) <{fastmathFlags = #llvm.fastmath<ninf>}> : (f64, f64) -> f64
      %38 = "llvm.fadd"(%fcst, %fcst) <{fastmathFlags = #llvm.fastmath<nsz>}> : (f64, f64) -> f64
      %39 = "llvm.fsub"(%fcst, %fcst) : (f64, f64) -> f64
      %40 = "llvm.fsub"(%fcst, %fcst) <{fastmathFlags = #llvm.fastmath<fast>}> : (f64, f64) -> f64
      %41 = "llvm.fsub"(%fcst, %fcst) <{fastmathFlags = #llvm.fastmath<nnan>}> : (f64, f64) -> f64
      %42 = "llvm.fsub"(%fcst, %fcst) <{fastmathFlags = #llvm.fastmath<ninf>}> : (f64, f64) -> f64
      %43 = "llvm.fsub"(%fcst, %fcst) <{fastmathFlags = #llvm.fastmath<nsz>}> : (f64, f64) -> f64
      %44 = "llvm.fmul"(%fcst, %fcst) : (f64, f64) -> f64
      %45 = "llvm.fmul"(%fcst, %fcst) <{fastmathFlags = #llvm.fastmath<fast>}> : (f64, f64) -> f64
      %46 = "llvm.fmul"(%fcst, %fcst) <{fastmathFlags = #llvm.fastmath<nnan>}> : (f64, f64) -> f64
      %47 = "llvm.fmul"(%fcst, %fcst) <{fastmathFlags = #llvm.fastmath<ninf>}> : (f64, f64) -> f64
      %48 = "llvm.fmul"(%fcst, %fcst) <{fastmathFlags = #llvm.fastmath<nsz>}> : (f64, f64) -> f64
      %49 = "llvm.fdiv"(%fcst, %fcst) : (f64, f64) -> f64
      %50 = "llvm.fdiv"(%fcst, %fcst) <{fastmathFlags = #llvm.fastmath<fast>}> : (f64, f64) -> f64
      %51 = "llvm.fdiv"(%fcst, %fcst) <{fastmathFlags = #llvm.fastmath<nnan>}> : (f64, f64) -> f64
      %52 = "llvm.fdiv"(%fcst, %fcst) <{fastmathFlags = #llvm.fastmath<ninf>}> : (f64, f64) -> f64
      %53 = "llvm.fdiv"(%fcst, %fcst) <{fastmathFlags = #llvm.fastmath<nsz>}> : (f64, f64) -> f64
      %54 = "llvm.frem"(%fcst, %fcst) <{fastmathFlags = #llvm.fastmath<none>}> : (f64, f64) -> f64
      %55 = "llvm.frem"(%fcst, %fcst) <{fastmathFlags = #llvm.fastmath<fast>}> : (f64, f64) -> f64
      %56 = "llvm.frem"(%fcst, %fcst) <{fastmathFlags = #llvm.fastmath<nnan>}> : (f64, f64) -> f64
      %57 = "llvm.frem"(%fcst, %fcst) <{fastmathFlags = #llvm.fastmath<ninf>}> : (f64, f64) -> f64
      %58 = "llvm.frem"(%fcst, %fcst) <{fastmathFlags = #llvm.fastmath<nsz>}> : (f64, f64) -> f64
      %59 = "llvm.frem"(%fcst, %fcst) <{fastmathFlags = #llvm.fastmath<nsz, nnan, ninf>}> : (f64, f64) -> f64
      %60 = "llvm.freeze"(%5) : (i32) -> i32
      %61 = "llvm.mlir.poison"() : () -> i64
      "llvm.return"(%arg7_0) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:       "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "llvm.module_flags"() <{"flags" = [#llvm.mlir.module_flag<error, "wchar_size", 4 : i32>, #llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<max, "PIE Level", 2 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>, #llvm.mlir.module_flag<max, "frame-pointer", 2 : i32>]}> : () -> ()
// CHECK-NEXT:     "llvm.func"()  <{"CConv" = #llvm.cconv<ccc>, "function_type" = !llvm.func<i32 (f64)>, "linkage" = #llvm.linkage<external>, "sym_name" = "myfunc", "unnamed_addr" = 0 : i64, "visibility_" = 0 : i64}> ({
// CHECK-NEXT:         ^{{.*}}(%arg7_0 : f64):
// CHECK-NEXT:       %{{.*}} = "llvm.mlir.constant"() <{"value" = 13 : i32}> : () -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.mlir.constant"() <{"value" = 1 : i32}> : () -> i1
// CHECK-NEXT:       %{{.*}} = "llvm.and"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.or"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.xor"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.intr.smax"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.intr.smin"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.intr.umax"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.intr.umin"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.add"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.add"(%{{.*}}, %{{.*}}) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.add"(%{{.*}}, %{{.*}}) <{"overflowFlags" = 2 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.add"(%{{.*}}, %{{.*}}) <{"overflowFlags" = 3 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.sub"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.mul"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.mul"(%{{.*}}, %{{.*}}) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.mul"(%{{.*}}, %{{.*}}) <{"overflowFlags" = 2 : i32}> : (i32, i32) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.mul"(%{{.*}}, %{{.*}}) <{"overflowFlags" = 3 : i32}> : (i32, i32) -> i32
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
// CHECK-NEXT:       %{{.*}} = "llvm.alloca"(%{{.*}}) <{"alignment" = 4 : i64, "elem_type" = i32, inalloca}> : (i32) -> !llvm.ptr
// CHECK-NEXT:       "llvm.store"(%{{.*}}, %{{.*}}) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 0 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:       "llvm.store"(%{{.*}}, %{{.*}}) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, invariantGroup, "noalias_scopes" = [], nontemporal, "tbaa" = [], volatile_}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT:       %{{.*}} = "llvm.load"(%{{.*}}) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 0 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.load"(%{{.*}}) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 1 : i64, invariant, invariantGroup, "noalias_scopes" = [], nontemporal, "tbaa" = [], volatile_}> : (!llvm.ptr) -> i32
// CHECK-NEXT:       "llvm.cond_br"(%{{.*}}, %{{.*}}, %{{.*}}) [^[[b1:.*]], ^[[b1]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
// CHECK-NEXT:     ^[[b1]](%{{.*}} : i32):
// CHECK-NEXT:       "llvm.br"(%{{.*}}) [^[[b2:.*]]] : (i32) -> ()
// CHECK-NEXT:     ^[[b2]](%{{.*}} : i32):
// CHECK-NEXT:       "llvm.return"(%{{.*}}) : (i32) -> ()
// CHECK-NEXT:     ^{{.*}}(%{{.*}} : !llvm.ptr):
// CHECK-NEXT:       %{{.*}} = "llvm.getelementptr"(%{{.*}}, %{{.*}}) <{"elem_type" = !llvm.struct<(i32, f32)>, "noWrapFlags" = 0 : i32, "rawConstantIndices" = array<i32: -2147483648, 0>}> : (!llvm.ptr, i1) -> !llvm.ptr
// CHECK-NEXT:       %{{.*}} = "llvm.fadd"(%arg7_0, %arg7_0) <{"fastmathFlags" = #llvm.fastmath<none>}> : (f64, f64) -> f64
// CHECK-NEXT:       %{{.*}} = "llvm.fadd"(%arg7_0, %arg7_0) <{"fastmathFlags" = #llvm.fastmath<fast>}> : (f64, f64) -> f64
// CHECK-NEXT:       %{{.*}} = "llvm.fadd"(%arg7_0, %arg7_0) <{"fastmathFlags" = #llvm.fastmath<nnan>}> : (f64, f64) -> f64
// CHECK-NEXT:       %{{.*}} = "llvm.fadd"(%arg7_0, %arg7_0) <{"fastmathFlags" = #llvm.fastmath<ninf>}> : (f64, f64) -> f64
// CHECK-NEXT:       %{{.*}} = "llvm.fadd"(%arg7_0, %arg7_0) <{"fastmathFlags" = #llvm.fastmath<nsz>}> : (f64, f64) -> f64
// CHECK-NEXT:       %{{.*}} = "llvm.fsub"(%arg7_0, %arg7_0) <{"fastmathFlags" = #llvm.fastmath<none>}> : (f64, f64) -> f64
// CHECK-NEXT:       %{{.*}} = "llvm.fsub"(%arg7_0, %arg7_0) <{"fastmathFlags" = #llvm.fastmath<fast>}> : (f64, f64) -> f64
// CHECK-NEXT:       %{{.*}} = "llvm.fsub"(%arg7_0, %arg7_0) <{"fastmathFlags" = #llvm.fastmath<nnan>}> : (f64, f64) -> f64
// CHECK-NEXT:       %{{.*}} = "llvm.fsub"(%arg7_0, %arg7_0) <{"fastmathFlags" = #llvm.fastmath<ninf>}> : (f64, f64) -> f64
// CHECK-NEXT:       %{{.*}} = "llvm.fsub"(%arg7_0, %arg7_0) <{"fastmathFlags" = #llvm.fastmath<nsz>}> : (f64, f64) -> f64
// CHECK-NEXT:       %{{.*}} = "llvm.fmul"(%arg7_0, %arg7_0) <{"fastmathFlags" = #llvm.fastmath<none>}> : (f64, f64) -> f64
// CHECK-NEXT:       %{{.*}} = "llvm.fmul"(%arg7_0, %arg7_0) <{"fastmathFlags" = #llvm.fastmath<fast>}> : (f64, f64) -> f64
// CHECK-NEXT:       %{{.*}} = "llvm.fmul"(%arg7_0, %arg7_0) <{"fastmathFlags" = #llvm.fastmath<nnan>}> : (f64, f64) -> f64
// CHECK-NEXT:       %{{.*}} = "llvm.fmul"(%arg7_0, %arg7_0) <{"fastmathFlags" = #llvm.fastmath<ninf>}> : (f64, f64) -> f64
// CHECK-NEXT:       %{{.*}} = "llvm.fmul"(%arg7_0, %arg7_0) <{"fastmathFlags" = #llvm.fastmath<nsz>}> : (f64, f64) -> f64
// CHECK-NEXT:       %{{.*}} = "llvm.fdiv"(%arg7_0, %arg7_0) <{"fastmathFlags" = #llvm.fastmath<none>}> : (f64, f64) -> f64
// CHECK-NEXT:       %{{.*}} = "llvm.fdiv"(%arg7_0, %arg7_0) <{"fastmathFlags" = #llvm.fastmath<fast>}> : (f64, f64) -> f64
// CHECK-NEXT:       %{{.*}} = "llvm.fdiv"(%arg7_0, %arg7_0) <{"fastmathFlags" = #llvm.fastmath<nnan>}> : (f64, f64) -> f64
// CHECK-NEXT:       %{{.*}} = "llvm.fdiv"(%arg7_0, %arg7_0) <{"fastmathFlags" = #llvm.fastmath<ninf>}> : (f64, f64) -> f64
// CHECK-NEXT:       %{{.*}} = "llvm.fdiv"(%arg7_0, %arg7_0) <{"fastmathFlags" = #llvm.fastmath<nsz>}> : (f64, f64) -> f64
// CHECK-NEXT:       %{{.*}} = "llvm.frem"(%arg7_0, %arg7_0) <{"fastmathFlags" = #llvm.fastmath<none>}> : (f64, f64) -> f64
// CHECK-NEXT:       %{{.*}} = "llvm.frem"(%arg7_0, %arg7_0) <{"fastmathFlags" = #llvm.fastmath<fast>}> : (f64, f64) -> f64
// CHECK-NEXT:       %{{.*}} = "llvm.frem"(%arg7_0, %arg7_0) <{"fastmathFlags" = #llvm.fastmath<nnan>}> : (f64, f64) -> f64
// CHECK-NEXT:       %{{.*}} = "llvm.frem"(%arg7_0, %arg7_0) <{"fastmathFlags" = #llvm.fastmath<ninf>}> : (f64, f64) -> f64
// CHECK-NEXT:       %{{.*}} = "llvm.frem"(%arg7_0, %arg7_0) <{"fastmathFlags" = #llvm.fastmath<nsz>}> : (f64, f64) -> f64
// CHECK-NEXT:       %{{.*}} = "llvm.frem"(%arg7_0, %arg7_0) <{"fastmathFlags" = #llvm.fastmath<fast>}> : (f64, f64) -> f64
// CHECK-NEXT:       %{{.*}} = "llvm.freeze"(%{{.*}}) : (i32) -> i32
// CHECK-NEXT:       %{{.*}} = "llvm.mlir.poison"() : () -> i64
// CHECK-NEXT:       "llvm.return"(%{{.*}}) : (i32) -> ()
// CHECK-NEXT:   }) : () -> ()
// CHECK-NEXT: }) : () -> ()
