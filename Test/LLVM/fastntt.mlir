// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

// This file contains a very naive implementation of the FastNTT algorithm, based on the heir pseudocode
// (https://github.com/google/heir/blob/1210ad37dc9531d6e60d8ddbce81dbd79f7626a6/lib/Dialect/Polynomial/Conversions/PolynomialToModArith/PolynomialToModArith.cpp#L1060) and lowered using the `Vcc` tool (see `Test/Vcc/fastntt.c`).

"builtin.module"() ({
  ^4():
    "llvm.module_flags"() <{"flags" = [#llvm.mlir.module_flag<error, "wchar_size", 4 : i32>, #llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<max, "PIE Level", 2 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>, #llvm.mlir.module_flag<max, "frame-pointer", 2 : i32>]}> : () -> ()
    "llvm.func"() <{"CConv" = #llvm.cconv<ccc>, always_inline, "arg_attrs" = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}], dso_local, "frame_pointer" = #llvm.framePointerKind<all>, "function_type" = !llvm.func<void (!llvm.ptr, i64, i64, !llvm.ptr, i64, i64)>, "linkage" = #llvm.linkage<external>, no_unwind, "passthrough" = [["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], "sym_name" = "fastNTT", "target_cpu" = "x86-64", "target_features" = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, "tune_cpu" = "generic", "unnamed_addr" = 0 : i64, "uwtable_kind" = #llvm.uwtableKind<async>, "visibility_" = 0 : i64}> ({
      ^7(%arg7_0 : !llvm.ptr, %arg7_1 : i64, %arg7_2 : i64, %arg7_3 : !llvm.ptr, %arg7_4 : i64, %arg7_5 : i64):
        %8 = "llvm.mlir.constant"() <{"value" = 0 : i64}> : () -> i64
        %9 = "llvm.mlir.constant"() <{"value" = 2 : i64}> : () -> i64
        %10 = "llvm.mlir.constant"() <{"value" = 1 : i64}> : () -> i64
        %11 = "llvm.icmp"(%arg7_4, %8) <{"predicate" = 1 : i64}> : (i64, i64) -> i1
        "llvm.cond_br"(%11) [^12, ^13] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
      ^12():
        "llvm.br"(%arg7_1) [^15] : (i64) -> ()
      ^13():
        "llvm.br"(%9) [^15] : (i64) -> ()
      ^15(%arg15_0 : i64):
        %18 = "llvm.icmp"(%arg7_4, %8) <{"predicate" = 1 : i64}> : (i64, i64) -> i1
        "llvm.cond_br"(%18) [^19, ^20] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
      ^19():
        "llvm.br"(%10) [^22] : (i64) -> ()
      ^20():
        %24 = "llvm.sdiv"(%arg7_5, %9) : (i64, i64) -> i64
        "llvm.br"(%24) [^22] : (i64) -> ()
      ^22(%arg22_0 : i64):
        %26 = "llvm.sdiv"(%arg7_1, %9) : (i64, i64) -> i64
        "llvm.br"(%arg22_0, %26, %8, %arg15_0) [^27] : (i64, i64, i64, i64) -> ()
      ^27(%arg27_0 : i64, %arg27_1 : i64, %arg27_2 : i64, %arg27_3 : i64):
        "llvm.br"(%8, %arg7_1) [^29] : (i64, i64) -> ()
      ^29(%arg29_0 : i64, %arg29_1 : i64):
        %31 = "llvm.icmp"(%arg29_1, %10) <{"predicate" = 4 : i64}> : (i64, i64) -> i1
        "llvm.cond_br"(%31) [^32, ^33] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
      ^32():
        %35 = "llvm.ashr"(%arg29_1, %10) : (i64, i64) -> i64
        %36 = "llvm.add"(%arg29_0, %10) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        "llvm.br"(%36, %35) [^29] : (i64, i64) -> ()
      ^33():
        %38 = "llvm.icmp"(%arg27_2, %arg29_0) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
        "llvm.cond_br"(%38) [^39, ^40] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
      ^39():
        "llvm.br"(%8) [^42] : (i64) -> ()
      ^42(%arg42_0 : i64):
        %44 = "llvm.sdiv"(%arg7_1, %arg27_3) : (i64, i64) -> i64
        %45 = "llvm.icmp"(%arg42_0, %44) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
        "llvm.cond_br"(%45) [^46, ^47] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
      ^46():
        "llvm.br"(%8) [^49] : (i64) -> ()
      ^49(%arg49_0 : i64):
        %51 = "llvm.sdiv"(%arg27_3, %9) : (i64, i64) -> i64
        %52 = "llvm.icmp"(%arg49_0, %51) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
        "llvm.cond_br"(%52) [^53, ^54] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
      ^53():
        %56 = "llvm.mul"(%arg42_0, %arg27_3) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        %57 = "llvm.add"(%56, %arg49_0) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        %58 = "llvm.getelementptr"(%arg7_0, %57) <{"elem_type" = i64, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %59 = "llvm.load"(%58) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i64
        %62 = "llvm.sdiv"(%arg27_3, %9) : (i64, i64) -> i64
        %63 = "llvm.add"(%57, %62) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        %64 = "llvm.getelementptr"(%arg7_0, %63) <{"elem_type" = i64, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %65 = "llvm.load"(%64) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i64
        %66 = "llvm.mul"(%9, %arg49_0) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        %67 = "llvm.add"(%66, %10) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        %68 = "llvm.mul"(%67, %arg27_1) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        %69 = "llvm.getelementptr"(%arg7_3, %68) <{"elem_type" = i64, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %70 = "llvm.load"(%69) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i64
        %71 = "llvm.mul"(%70, %65) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        %72 = "llvm.srem"(%71, %arg7_2) : (i64, i64) -> i64
        %73 = "llvm.add"(%59, %72) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        %74 = "llvm.srem"(%73, %arg7_2) : (i64, i64) -> i64
        %77 = "llvm.sub"(%59, %72) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        %78 = "llvm.add"(%77, %arg7_2) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        %79 = "llvm.srem"(%78, %arg7_2) : (i64, i64) -> i64
        %82 = "llvm.getelementptr"(%arg7_0, %57) <{"elem_type" = i64, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%74, %82) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i64, !llvm.ptr) -> ()
        %88 = "llvm.getelementptr"(%arg7_0, %63) <{"elem_type" = i64, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%79, %88) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i64, !llvm.ptr) -> ()
        "llvm.br"() [^90] : () -> ()
      ^90():
        %92 = "llvm.add"(%arg49_0, %10) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        "llvm.br"(%92) [^49] : (i64) -> ()
      ^54():
        "llvm.br"() [^94] : () -> ()
      ^94():
        %96 = "llvm.add"(%arg42_0, %10) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        "llvm.br"(%96) [^42] : (i64) -> ()
      ^47():
        %98 = "llvm.sdiv"(%arg27_1, %9) : (i64, i64) -> i64
        %99 = "llvm.icmp"(%arg7_4, %8) <{"predicate" = 1 : i64}> : (i64, i64) -> i1
        "llvm.cond_br"(%99) [^100, ^101] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
      ^100():
        %103 = "llvm.sdiv"(%arg27_3, %9) : (i64, i64) -> i64
        "llvm.br"(%103) [^104] : (i64) -> ()
      ^101():
        %125 = "llvm.add"(%arg27_3, %arg27_3) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        "llvm.br"(%125) [^104] : (i64) -> ()
      ^104(%arg104_0 : i64):
        %108 = "llvm.icmp"(%arg7_4, %8) <{"predicate" = 1 : i64}> : (i64, i64) -> i1
        "llvm.cond_br"(%108) [^109, ^110] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
      ^109():
        %124 = "llvm.add"(%arg27_0, %arg27_0) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        "llvm.br"(%124) [^113] : (i64) -> ()
      ^110():
        %115 = "llvm.sdiv"(%arg27_0, %9) : (i64, i64) -> i64
        "llvm.br"(%115) [^113] : (i64) -> ()
      ^113(%arg113_0 : i64):
        "llvm.br"() [^117] : () -> ()
      ^117():
        %119 = "llvm.add"(%arg27_2, %10) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        "llvm.br"(%arg113_0, %98, %119, %arg104_0) [^27] : (i64, i64, i64, i64) -> ()
      ^40():
        "llvm.return"() : () -> ()
    }) : () -> ()
}) {"dlti.dl_spec" = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, "llvm.ident" = "Ubuntu clang version 18.1.3 (1ubuntu1)", "llvm.module_asm" = [], "llvm.target_triple" = "x86_64-pc-linux-gnu"} : () -> ()

// CHECK: "builtin.module"() ({
// CHECK-NEXT:   ^4():
// CHECK-NEXT:     "llvm.module_flags"() <{"flags" = [#llvm.mlir.module_flag<error, "wchar_size", 4 : i32>, #llvm.mlir.module_flag<min, "PIC Level", 2 : i32>, #llvm.mlir.module_flag<max, "PIE Level", 2 : i32>, #llvm.mlir.module_flag<max, "uwtable", 2 : i32>, #llvm.mlir.module_flag<max, "frame-pointer", 2 : i32>]}> : () -> ()
// CHECK-NEXT:     "llvm.func"() <{"CConv" = #llvm.cconv<ccc>, always_inline, "arg_attrs" = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}], dso_local, "frame_pointer" = #llvm.framePointerKind<all>, "function_type" = !llvm.func<void (!llvm.ptr, i64, i64, !llvm.ptr, i64, i64)>, "linkage" = #llvm.linkage<external>, no_unwind, "passthrough" = {{\[\[}}"min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], "sym_name" = "fastNTT", "target_cpu" = "x86-64", "target_features" = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, "tune_cpu" = "generic", "unnamed_addr" = 0 : i64, "uwtable_kind" = #llvm.uwtableKind<async>, "visibility_" = 0 : i64}> ({
// CHECK-NEXT:       ^7(%[[VAL_0:.*]] : !llvm.ptr, %[[VAL_1:.*]] : i64, %[[VAL_2:.*]] : i64, %[[VAL_3:.*]] : !llvm.ptr, %[[VAL_4:.*]] : i64, %[[VAL_5:.*]] : i64):
// CHECK-NEXT:         %[[VAL_6:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i64}> : () -> i64
// CHECK-NEXT:         %[[VAL_7:.*]] = "llvm.mlir.constant"() <{"value" = 2 : i64}> : () -> i64
// CHECK-NEXT:         %[[VAL_8:.*]] = "llvm.mlir.constant"() <{"value" = 1 : i64}> : () -> i64
// CHECK-NEXT:         %[[VAL_9:.*]] = "llvm.icmp"(%[[VAL_4]], %[[VAL_6]]) <{"predicate" = 1 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[VAL_9]]) [^12, ^13] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^12():
// CHECK-NEXT:         "llvm.br"(%[[VAL_1]]) [^15] : (i64) -> ()
// CHECK-NEXT:       ^13():
// CHECK-NEXT:         "llvm.br"(%[[VAL_7]]) [^15] : (i64) -> ()
// CHECK-NEXT:       ^15(%[[VAL_10:.*]] : i64):
// CHECK-NEXT:         %[[VAL_11:.*]] = "llvm.icmp"(%[[VAL_4]], %[[VAL_6]]) <{"predicate" = 1 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[VAL_11]]) [^19, ^20] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^19():
// CHECK-NEXT:         "llvm.br"(%[[VAL_8]]) [^22] : (i64) -> ()
// CHECK-NEXT:       ^20():
// CHECK-NEXT:         %[[VAL_12:.*]] = "llvm.sdiv"(%[[VAL_5]], %[[VAL_7]]) : (i64, i64) -> i64
// CHECK-NEXT:         "llvm.br"(%[[VAL_12]]) [^22] : (i64) -> ()
// CHECK-NEXT:       ^22(%[[VAL_13:.*]] : i64):
// CHECK-NEXT:         %[[VAL_14:.*]] = "llvm.sdiv"(%[[VAL_1]], %[[VAL_7]]) : (i64, i64) -> i64
// CHECK-NEXT:         "llvm.br"(%[[VAL_13]], %[[VAL_14]], %[[VAL_6]], %[[VAL_10]]) [^27] : (i64, i64, i64, i64) -> ()
// CHECK-NEXT:       ^27(%[[VAL_15:.*]] : i64, %[[VAL_16:.*]] : i64, %[[VAL_17:.*]] : i64, %[[VAL_18:.*]] : i64):
// CHECK-NEXT:         "llvm.br"(%[[VAL_6]], %[[VAL_1]]) [^29] : (i64, i64) -> ()
// CHECK-NEXT:       ^29(%[[VAL_19:.*]] : i64, %[[VAL_20:.*]] : i64):
// CHECK-NEXT:         %[[VAL_21:.*]] = "llvm.icmp"(%[[VAL_20]], %[[VAL_8]]) <{"predicate" = 4 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[VAL_21]]) [^32, ^33] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^32():
// CHECK-NEXT:         %[[VAL_22:.*]] = "llvm.ashr"(%[[VAL_20]], %[[VAL_8]]) : (i64, i64) -> i64
// CHECK-NEXT:         %[[VAL_23:.*]] = "llvm.add"(%[[VAL_19]], %[[VAL_8]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         "llvm.br"(%[[VAL_23]], %[[VAL_22]]) [^29] : (i64, i64) -> ()
// CHECK-NEXT:       ^33():
// CHECK-NEXT:         %[[VAL_24:.*]] = "llvm.icmp"(%[[VAL_17]], %[[VAL_19]]) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[VAL_24]]) [^39, ^40] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^39():
// CHECK-NEXT:         "llvm.br"(%[[VAL_6]]) [^42] : (i64) -> ()
// CHECK-NEXT:       ^42(%[[VAL_25:.*]] : i64):
// CHECK-NEXT:         %[[VAL_26:.*]] = "llvm.sdiv"(%[[VAL_1]], %[[VAL_18]]) : (i64, i64) -> i64
// CHECK-NEXT:         %[[VAL_27:.*]] = "llvm.icmp"(%[[VAL_25]], %[[VAL_26]]) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[VAL_27]]) [^46, ^47] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^46():
// CHECK-NEXT:         "llvm.br"(%[[VAL_6]]) [^49] : (i64) -> ()
// CHECK-NEXT:       ^49(%[[VAL_28:.*]] : i64):
// CHECK-NEXT:         %[[VAL_29:.*]] = "llvm.sdiv"(%[[VAL_18]], %[[VAL_7]]) : (i64, i64) -> i64
// CHECK-NEXT:         %[[VAL_30:.*]] = "llvm.icmp"(%[[VAL_28]], %[[VAL_29]]) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[VAL_30]]) [^53, ^54] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^53():
// CHECK-NEXT:         %[[VAL_31:.*]] = "llvm.mul"(%[[VAL_25]], %[[VAL_18]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         %[[VAL_32:.*]] = "llvm.add"(%[[VAL_31]], %[[VAL_28]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         %[[VAL_33:.*]] = "llvm.getelementptr"(%[[VAL_0]], %[[VAL_32]]) <{"elem_type" = i64, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[VAL_34:.*]] = "llvm.load"(%[[VAL_33]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i64
// CHECK-NEXT:         %[[VAL_35:.*]] = "llvm.sdiv"(%[[VAL_18]], %[[VAL_7]]) : (i64, i64) -> i64
// CHECK-NEXT:         %[[VAL_36:.*]] = "llvm.add"(%[[VAL_32]], %[[VAL_35]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         %[[VAL_37:.*]] = "llvm.getelementptr"(%[[VAL_0]], %[[VAL_36]]) <{"elem_type" = i64, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[VAL_38:.*]] = "llvm.load"(%[[VAL_37]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i64
// CHECK-NEXT:         %[[VAL_39:.*]] = "llvm.mul"(%[[VAL_7]], %[[VAL_28]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         %[[VAL_40:.*]] = "llvm.add"(%[[VAL_39]], %[[VAL_8]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         %[[VAL_41:.*]] = "llvm.mul"(%[[VAL_40]], %[[VAL_16]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         %[[VAL_42:.*]] = "llvm.getelementptr"(%[[VAL_3]], %[[VAL_41]]) <{"elem_type" = i64, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         %[[VAL_43:.*]] = "llvm.load"(%[[VAL_42]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i64
// CHECK-NEXT:         %[[VAL_44:.*]] = "llvm.mul"(%[[VAL_43]], %[[VAL_38]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         %[[VAL_45:.*]] = "llvm.srem"(%[[VAL_44]], %[[VAL_2]]) : (i64, i64) -> i64
// CHECK-NEXT:         %[[VAL_46:.*]] = "llvm.add"(%[[VAL_34]], %[[VAL_45]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         %[[VAL_47:.*]] = "llvm.srem"(%[[VAL_46]], %[[VAL_2]]) : (i64, i64) -> i64
// CHECK-NEXT:         %[[VAL_48:.*]] = "llvm.sub"(%[[VAL_34]], %[[VAL_45]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         %[[VAL_49:.*]] = "llvm.add"(%[[VAL_48]], %[[VAL_2]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         %[[VAL_50:.*]] = "llvm.srem"(%[[VAL_49]], %[[VAL_2]]) : (i64, i64) -> i64
// CHECK-NEXT:         %[[VAL_51:.*]] = "llvm.getelementptr"(%[[VAL_0]], %[[VAL_32]]) <{"elem_type" = i64, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[VAL_47]], %[[VAL_51]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i64, !llvm.ptr) -> ()
// CHECK-NEXT:         %[[VAL_52:.*]] = "llvm.getelementptr"(%[[VAL_0]], %[[VAL_36]]) <{"elem_type" = i64, "noWrapFlags" = 3 : i32, "rawConstantIndices" = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
// CHECK-NEXT:         "llvm.store"(%[[VAL_50]], %[[VAL_52]]) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 8 : i64, "noalias_scopes" = [], "tbaa" = []}> : (i64, !llvm.ptr) -> ()
// CHECK-NEXT:         "llvm.br"() [^80] : () -> ()
// CHECK-NEXT:       ^80():
// CHECK-NEXT:         %[[VAL_53:.*]] = "llvm.add"(%[[VAL_28]], %[[VAL_8]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         "llvm.br"(%[[VAL_53]]) [^49] : (i64) -> ()
// CHECK-NEXT:       ^54():
// CHECK-NEXT:         "llvm.br"() [^84] : () -> ()
// CHECK-NEXT:       ^84():
// CHECK-NEXT:         %[[VAL_54:.*]] = "llvm.add"(%[[VAL_25]], %[[VAL_8]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         "llvm.br"(%[[VAL_54]]) [^42] : (i64) -> ()
// CHECK-NEXT:       ^47():
// CHECK-NEXT:         %[[VAL_55:.*]] = "llvm.sdiv"(%[[VAL_16]], %[[VAL_7]]) : (i64, i64) -> i64
// CHECK-NEXT:         %[[VAL_56:.*]] = "llvm.icmp"(%[[VAL_4]], %[[VAL_6]]) <{"predicate" = 1 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[VAL_56]]) [^90, ^91] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^90():
// CHECK-NEXT:         %[[VAL_57:.*]] = "llvm.sdiv"(%[[VAL_18]], %[[VAL_7]]) : (i64, i64) -> i64
// CHECK-NEXT:         "llvm.br"(%[[VAL_57]]) [^94] : (i64) -> ()
// CHECK-NEXT:       ^91():
// CHECK-NEXT:         %[[VAL_58:.*]] = "llvm.add"(%[[VAL_18]], %[[VAL_18]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         "llvm.br"(%[[VAL_58]]) [^94] : (i64) -> ()
// CHECK-NEXT:       ^94(%[[VAL_59:.*]] : i64):
// CHECK-NEXT:         %[[VAL_60:.*]] = "llvm.icmp"(%[[VAL_4]], %[[VAL_6]]) <{"predicate" = 1 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:         "llvm.cond_br"(%[[VAL_60]]) [^99, ^100] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
// CHECK-NEXT:       ^99():
// CHECK-NEXT:         %[[VAL_61:.*]] = "llvm.add"(%[[VAL_15]], %[[VAL_15]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         "llvm.br"(%[[VAL_61]]) [^103] : (i64) -> ()
// CHECK-NEXT:       ^100():
// CHECK-NEXT:         %[[VAL_62:.*]] = "llvm.sdiv"(%[[VAL_15]], %[[VAL_7]]) : (i64, i64) -> i64
// CHECK-NEXT:         "llvm.br"(%[[VAL_62]]) [^103] : (i64) -> ()
// CHECK-NEXT:       ^103(%[[VAL_63:.*]] : i64):
// CHECK-NEXT:         "llvm.br"() [^107] : () -> ()
// CHECK-NEXT:       ^107():
// CHECK-NEXT:         %[[VAL_64:.*]] = "llvm.add"(%[[VAL_17]], %[[VAL_8]]) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
// CHECK-NEXT:         "llvm.br"(%[[VAL_63]], %[[VAL_55]], %[[VAL_64]], %[[VAL_59]]) [^27] : (i64, i64, i64, i64) -> ()
// CHECK-NEXT:       ^40():
// CHECK-NEXT:         "llvm.return"() : () -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) {"dlti.dl_spec" = #dlti.dl_spec<!llvm.ptr<270> = dense<32> : vector<4xi64>, !llvm.ptr<271> = dense<32> : vector<4xi64>, !llvm.ptr<272> = dense<64> : vector<4xi64>, i64 = dense<64> : vector<2xi64>, i128 = dense<128> : vector<2xi64>, f80 = dense<128> : vector<2xi64>, !llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little", "dlti.mangling_mode" = "e", "dlti.legal_int_widths" = array<i32: 8, 16, 32, 64>, "dlti.stack_alignment" = 128 : i64>, "llvm.ident" = "Ubuntu clang version 18.1.3 (1ubuntu1)", "llvm.module_asm" = [], "llvm.target_triple" = "x86_64-pc-linux-gnu"} : () -> ()
