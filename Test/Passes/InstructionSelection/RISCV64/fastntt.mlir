// RUN: veir-opt %s -p=isel-br-riscv64,isel-riscv64,reconcile-cast,riscv-combine | filecheck %s

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


// CHECK:       "builtin.module"() ({
// CHECK-NEXT:    ^[[BB_ENTRY:[a-zA-Z0-9_]+]]():
// CHECK-NEXT:      "llvm.module_flags"()
// CHECK-NEXT:      "llvm.func"() <{"CConv" = #llvm.cconv<ccc>, always_inline, "arg_attrs" = [{llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}, {llvm.noundef}], dso_local, "frame_pointer" = #llvm.framePointerKind<all>, "function_type" = !llvm.func<void (!llvm.ptr, i64, i64, !llvm.ptr, i64, i64)>, "linkage" = #llvm.linkage<external>, no_unwind, "passthrough" = [["min-legal-vector-width", "0"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "x86-64"]], "sym_name" = "fastNTT", "target_cpu" = "x86-64", "target_features" = #llvm.target_features<["+cmov", "+cx8", "+fxsr", "+mmx", "+sse", "+sse2", "+x87"]>, "tune_cpu" = "generic", "unnamed_addr" = 0 : i64, "uwtable_kind" = #llvm.uwtableKind<async>, "visibility_" = 0 : i64}> ({
// CHECK-NEXT:        ^[[BB_FUNC_ENTRY:[a-zA-Z0-9_]+]](%{{.*}}: !llvm.ptr, %{{.*}}: i64, %{{.*}}: i64, %{{.*}}: !llvm.ptr, %{{.*}}: i64, %{{.*}}: i64):
// CHECK-NEXT:          %[[REG_C0:[0-9]+]] = "rv64.get_register"() : () -> !riscv.reg<x0>
// CHECK-NEXT:          %[[REG_C2:[0-9]+]] = "riscv.li"() <{"value" = 2 : i64}> : () -> !riscv.reg
// CHECK-NEXT:          %[[REG_C1:[0-9]+]] = "riscv.li"() <{"value" = 1 : i64}> : () -> !riscv.reg
// CHECK-NEXT:          %[[REG_CAST0:[0-9]+]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
// CHECK-NEXT:          %[[REG_C0_2:[0-9]+]] = "rv64.get_register"() : () -> !riscv.reg<x0>
// CHECK-NEXT:          %[[REG_SLTU0:[0-9]+]] = "riscv.sltu"(%[[REG_C0_2]], %[[REG_CAST0]]) : (!riscv.reg<x0>, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          %[[REG_CAST1:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[REG_SLTU0]]) : (!riscv.reg) -> i1
// CHECK-NEXT:          %[[REG_CAST2:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[REG_CAST1]]) : (i1) -> !riscv.reg
// CHECK-NEXT:          "riscv_cf.bnez"(%[[REG_CAST2]]) [^[[BB_12:[0-9]+]], ^[[BB_13:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
// CHECK-NEXT:      ^[[BB_12]]():
// CHECK-NEXT:          %[[REG_CAST3:[0-9]+]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
// CHECK-NEXT:          "riscv_cf.branch"(%[[REG_CAST3]]) [^[[BB_15:[0-9]+]]] : (!riscv.reg) -> ()
// CHECK-NEXT:      ^[[BB_13]]():
// CHECK-NEXT:          "riscv_cf.branch"(%[[REG_C2]]) [^[[BB_15]]] : (!riscv.reg) -> ()
// CHECK-NEXT:      ^[[BB_15]](%{{.*}}: !riscv.reg):
// CHECK-NEXT:          %[[REG_CAST4:[0-9]+]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
// CHECK-NEXT:          %[[REG_C0_3:[0-9]+]] = "rv64.get_register"() : () -> !riscv.reg<x0>
// CHECK-NEXT:          %[[REG_SLTU1:[0-9]+]] = "riscv.sltu"(%[[REG_C0_3]], %[[REG_CAST4]]) : (!riscv.reg<x0>, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          %[[REG_CAST5:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[REG_SLTU1]]) : (!riscv.reg) -> i1
// CHECK-NEXT:          %[[REG_CAST6:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[REG_CAST5]]) : (i1) -> !riscv.reg
// CHECK-NEXT:          "riscv_cf.bnez"(%[[REG_CAST6]]) [^[[BB_19:[0-9]+]], ^[[BB_20:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
// CHECK-NEXT:      ^[[BB_19]]():
// CHECK-NEXT:          "riscv_cf.branch"(%[[REG_C1]]) [^[[BB_22:[0-9]+]]] : (!riscv.reg) -> ()
// CHECK-NEXT:      ^[[BB_20]]():
// CHECK-NEXT:          %[[REG_CAST7:[0-9]+]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
// CHECK-NEXT:          %[[REG_DIV0:[0-9]+]] = "riscv.div"(%[[REG_CAST7]], %[[REG_C2]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          "riscv_cf.branch"(%[[REG_DIV0]]) [^[[BB_22]]] : (!riscv.reg) -> ()
// CHECK-NEXT:      ^[[BB_22]](%{{.*}}: !riscv.reg):
// CHECK-NEXT:          %[[REG_CAST8:[0-9]+]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
// CHECK-NEXT:          %[[REG_DIV1:[0-9]+]] = "riscv.div"(%[[REG_CAST8]], %[[REG_C2]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          "riscv_cf.branch"({{.*}}, %[[REG_DIV1]], %[[REG_C0]], {{.*}}) [^[[BB_27:[0-9]+]]] : (!riscv.reg, !riscv.reg, !riscv.reg<x0>, !riscv.reg) -> ()
// CHECK-NEXT:      ^[[BB_27]]({{.*}}):
// CHECK-NEXT:          %[[REG_CAST9:[0-9]+]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
// CHECK-NEXT:          "riscv_cf.branch"(%[[REG_C0]], %[[REG_CAST9]]) [^[[BB_29:[0-9]+]]] : (!riscv.reg<x0>, !riscv.reg) -> ()
// CHECK-NEXT:      ^[[BB_29]]({{.*}}):
// CHECK-NEXT:          %[[REG_SLT0:[0-9]+]] = "riscv.slt"(%[[REG_C1]], {{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          %[[REG_CAST10:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[REG_SLT0]]) : (!riscv.reg) -> i1
// CHECK-NEXT:          %[[REG_CAST11:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[REG_CAST10]]) : (i1) -> !riscv.reg
// CHECK-NEXT:          "riscv_cf.bnez"(%[[REG_CAST11]]) [^[[BB_32:[0-9]+]], ^[[BB_33:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
// CHECK-NEXT:      ^[[BB_32]]():
// CHECK-NEXT:          %[[REG_SRA0:[0-9]+]] = "riscv.sra"({{.*}}, %[[REG_C1]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          %[[REG_ADD0:[0-9]+]] = "riscv.add"(%[[REG_C1]], {{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          "riscv_cf.branch"(%[[REG_ADD0]], %[[REG_SRA0]]) [^[[BB_29]]] : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:      ^[[BB_33]]():
// CHECK-NEXT:          %[[REG_SLT1:[0-9]+]] = "riscv.slt"({{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          %[[REG_CAST12:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[REG_SLT1]]) : (!riscv.reg) -> i1
// CHECK-NEXT:          %[[REG_CAST13:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[REG_CAST12]]) : (i1) -> !riscv.reg
// CHECK-NEXT:          "riscv_cf.bnez"(%[[REG_CAST13]]) [^[[BB_39:[0-9]+]], ^[[BB_40:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
// CHECK-NEXT:      ^[[BB_39]]():
// CHECK-NEXT:          "riscv_cf.branch"(%[[REG_C0]]) [^[[BB_42:[0-9]+]]] : (!riscv.reg<x0>) -> ()
// CHECK-NEXT:      ^[[BB_42]](%[[ARG_42_0:[a-zA-Z0-9_]+]] : !riscv.reg):
// CHECK-NEXT:          %[[REG_CAST14:[0-9]+]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
// CHECK-NEXT:          %[[REG_DIV2:[0-9]+]] = "riscv.div"(%[[REG_CAST14]], {{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          %[[REG_SLT2:[0-9]+]] = "riscv.slt"(%[[ARG_42_0]], %[[REG_DIV2]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          %[[REG_CAST15:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[REG_SLT2]]) : (!riscv.reg) -> i1
// CHECK-NEXT:          %[[REG_CAST16:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[REG_CAST15]]) : (i1) -> !riscv.reg
// CHECK-NEXT:          "riscv_cf.bnez"(%[[REG_CAST16]]) [^[[BB_46:[0-9]+]], ^[[BB_47:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
// CHECK-NEXT:      ^[[BB_46]]():
// CHECK-NEXT:          "riscv_cf.branch"(%[[REG_C0]]) [^[[BB_49:[0-9]+]]] : (!riscv.reg<x0>) -> ()
// CHECK-NEXT:      ^[[BB_49]](%[[ARG_49_0:[a-zA-Z0-9_]+]] : !riscv.reg):
// CHECK-NEXT:          %[[REG_DIV3:[0-9]+]] = "riscv.div"({{.*}}, %[[REG_C2]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          %[[REG_SLT3:[0-9]+]] = "riscv.slt"(%[[ARG_49_0]], %[[REG_DIV3]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          %[[REG_CAST17:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[REG_SLT3]]) : (!riscv.reg) -> i1
// CHECK-NEXT:          %[[REG_CAST18:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[REG_CAST17]]) : (i1) -> !riscv.reg
// CHECK-NEXT:          "riscv_cf.bnez"(%[[REG_CAST18]]) [^[[BB_53:[0-9]+]], ^[[BB_54:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
// CHECK-NEXT:      ^[[BB_53]]():
// CHECK-NEXT:          %[[REG_MUL0:[0-9]+]] = "riscv.mul"({{.*}}, %[[ARG_42_0]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          %[[REG_ADD1:[0-9]+]] = "riscv.add"(%[[ARG_49_0]], %[[REG_MUL0]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          %[[REG_CAST19:[0-9]+]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:          %[[REG_SH3ADD0:[0-9]+]] = "riscv.sh3add"(%[[REG_ADD1]], %[[REG_CAST19]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          %[[REG_CAST20:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[REG_SH3ADD0]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:          %[[REG_CAST21:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[REG_CAST20]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:          %[[REG_LD0:[0-9]+]] = "riscv.ld"(%[[REG_CAST21]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:          %[[REG_DIV4:[0-9]+]] = "riscv.div"({{.*}}, %[[REG_C2]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          %[[REG_ADD2:[0-9]+]] = "riscv.add"(%[[REG_DIV4]], %[[REG_ADD1]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          %[[REG_CAST22:[0-9]+]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:          %[[REG_SH3ADD1:[0-9]+]] = "riscv.sh3add"(%[[REG_ADD2]], %[[REG_CAST22]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          %[[REG_CAST23:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[REG_SH3ADD1]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:          %[[REG_CAST24:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[REG_CAST23]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:          %[[REG_LD1:[0-9]+]] = "riscv.ld"(%[[REG_CAST24]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:          %[[REG_MUL1:[0-9]+]] = "riscv.mul"(%[[ARG_49_0]], %[[REG_C2]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          %[[REG_ADD3:[0-9]+]] = "riscv.add"(%[[REG_C1]], %[[REG_MUL1]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          %[[REG_MUL2:[0-9]+]] = "riscv.mul"({{.*}}, %[[REG_ADD3]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          %[[REG_CAST25:[0-9]+]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:          %[[REG_SH3ADD2:[0-9]+]] = "riscv.sh3add"(%[[REG_MUL2]], %[[REG_CAST25]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          %[[REG_CAST26:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[REG_SH3ADD2]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:          %[[REG_CAST27:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[REG_CAST26]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:          %[[REG_LD2:[0-9]+]] = "riscv.ld"(%[[REG_CAST27]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:          %[[REG_MUL3:[0-9]+]] = "riscv.mul"(%[[REG_LD1]], %[[REG_LD2]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          %[[REG_CAST28:[0-9]+]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
// CHECK-NEXT:          %[[REG_REM0:[0-9]+]] = "riscv.rem"(%[[REG_MUL3]], %[[REG_CAST28]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          %[[REG_ADD4:[0-9]+]] = "riscv.add"(%[[REG_REM0]], %[[REG_LD0]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          %[[REG_CAST29:[0-9]+]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
// CHECK-NEXT:          %[[REG_REM1:[0-9]+]] = "riscv.rem"(%[[REG_ADD4]], %[[REG_CAST29]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          %[[REG_SUB0:[0-9]+]] = "riscv.sub"(%[[REG_LD0]], %[[REG_REM0]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          %[[REG_CAST30:[0-9]+]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
// CHECK-NEXT:          %[[REG_ADD5:[0-9]+]] = "riscv.add"(%[[REG_CAST30]], %[[REG_SUB0]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          %[[REG_CAST31:[0-9]+]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
// CHECK-NEXT:          %[[REG_REM2:[0-9]+]] = "riscv.rem"(%[[REG_ADD5]], %[[REG_CAST31]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          %[[REG_CAST32:[0-9]+]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:          %[[REG_SH3ADD3:[0-9]+]] = "riscv.sh3add"(%[[REG_ADD1]], %[[REG_CAST32]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          %[[REG_CAST33:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[REG_SH3ADD3]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:          %[[REG_CAST34:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[REG_CAST33]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:          "riscv.sd"(%[[REG_CAST34]], %[[REG_REM1]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:          %[[REG_CAST35:[0-9]+]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:          %[[REG_SH3ADD4:[0-9]+]] = "riscv.sh3add"(%[[REG_ADD2]], %[[REG_CAST35]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          %[[REG_CAST36:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[REG_SH3ADD4]]) : (!riscv.reg) -> !llvm.ptr
// CHECK-NEXT:          %[[REG_CAST37:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[REG_CAST36]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:          "riscv.sd"(%[[REG_CAST37]], %[[REG_REM2]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:          "riscv_cf.branch"() [^[[BB_80:[0-9]+]]] : () -> ()
// CHECK-NEXT:      ^[[BB_80]]():
// CHECK-NEXT:          %[[REG_ADD6:[0-9]+]] = "riscv.add"(%[[REG_C1]], %[[ARG_49_0]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          "riscv_cf.branch"(%[[REG_ADD6]]) [^[[BB_49]]] : (!riscv.reg) -> ()
// CHECK-NEXT:      ^[[BB_54]]():
// CHECK-NEXT:          "riscv_cf.branch"() [^[[BB_84:[0-9]+]]] : () -> ()
// CHECK-NEXT:      ^[[BB_84]]():
// CHECK-NEXT:          %[[REG_ADD7:[0-9]+]] = "riscv.add"(%[[REG_C1]], %[[ARG_42_0]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          "riscv_cf.branch"(%[[REG_ADD7]]) [^[[BB_42]]] : (!riscv.reg) -> ()
// CHECK-NEXT:      ^[[BB_47]]():
// CHECK-NEXT:          %[[REG_DIV5:[0-9]+]] = "riscv.div"({{.*}}, %[[REG_C2]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          %[[REG_CAST38:[0-9]+]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
// CHECK-NEXT:          %[[REG_C0_4:[0-9]+]] = "rv64.get_register"() : () -> !riscv.reg<x0>
// CHECK-NEXT:          %[[REG_SLTU2:[0-9]+]] = "riscv.sltu"(%[[REG_C0_4]], %[[REG_CAST38]]) : (!riscv.reg<x0>, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          %[[REG_CAST39:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[REG_SLTU2]]) : (!riscv.reg) -> i1
// CHECK-NEXT:          %[[REG_CAST40:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[REG_CAST39]]) : (i1) -> !riscv.reg
// CHECK-NEXT:          "riscv_cf.bnez"(%[[REG_CAST40]]) [^[[BB_90:[0-9]+]], ^[[BB_91:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
// CHECK-NEXT:      ^[[BB_90]]():
// CHECK-NEXT:          %[[REG_DIV6:[0-9]+]] = "riscv.div"({{.*}}, %[[REG_C2]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          "riscv_cf.branch"(%[[REG_DIV6]]) [^[[BB_94:[0-9]+]]] : (!riscv.reg) -> ()
// CHECK-NEXT:      ^[[BB_91]]():
// CHECK-NEXT:          %[[REG_ADD8:[0-9]+]] = "riscv.add"({{.*}}, {{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          "riscv_cf.branch"(%[[REG_ADD8]]) [^[[BB_94]]] : (!riscv.reg) -> ()
// CHECK-NEXT:      ^[[BB_94]](%[[ARG_94_0:[a-zA-Z0-9_]+]] : !riscv.reg):
// CHECK-NEXT:          %[[REG_CAST41:[0-9]+]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
// CHECK-NEXT:          %[[REG_C0_5:[0-9]+]] = "rv64.get_register"() : () -> !riscv.reg<x0>
// CHECK-NEXT:          %[[REG_SLTU3:[0-9]+]] = "riscv.sltu"(%[[REG_C0_5]], %[[REG_CAST41]]) : (!riscv.reg<x0>, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          %[[REG_CAST42:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[REG_SLTU3]]) : (!riscv.reg) -> i1
// CHECK-NEXT:          %[[REG_CAST43:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[REG_CAST42]]) : (i1) -> !riscv.reg
// CHECK-NEXT:          "riscv_cf.bnez"(%[[REG_CAST43]]) [^[[BB_99:[0-9]+]], ^[[BB_100:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
// CHECK-NEXT:      ^[[BB_99]]():
// CHECK-NEXT:          %[[REG_ADD9:[0-9]+]] = "riscv.add"({{.*}}, {{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          "riscv_cf.branch"(%[[REG_ADD9]]) [^[[BB_103:[0-9]+]]] : (!riscv.reg) -> ()
// CHECK-NEXT:      ^[[BB_100]]():
// CHECK-NEXT:          %[[REG_DIV7:[0-9]+]] = "riscv.div"({{.*}}, %[[REG_C2]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          "riscv_cf.branch"(%[[REG_DIV7]]) [^[[BB_103]]] : (!riscv.reg) -> ()
// CHECK-NEXT:      ^[[BB_103]](%[[ARG_103_0:[a-zA-Z0-9_]+]] : !riscv.reg):
// CHECK-NEXT:          "riscv_cf.branch"() [^[[BB_107:[0-9]+]]] : () -> ()
// CHECK-NEXT:      ^[[BB_107]]():
// CHECK-NEXT:          %[[REG_ADD10:[0-9]+]] = "riscv.add"(%[[REG_C1]], {{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:          "riscv_cf.branch"(%[[ARG_103_0]], %[[REG_DIV5]], %[[REG_ADD10]], %[[ARG_94_0]]) [^[[BB_27]]] : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:      ^[[BB_40]]():
// CHECK-NEXT:          "llvm.return"() : () -> ()
// CHECK-NEXT:    })
// CHECK:         "llvm.target_triple" = "x86_64-pc-linux-gnu"