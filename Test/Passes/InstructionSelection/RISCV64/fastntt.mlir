// RUN: veir-opt %s -p=isel-sdag-riscv64,isel-br-riscv64,isel-riscv64,reconcile-cast,riscv-combine,dce | filecheck %s

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

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^[[bb4:[0-9]+]]():
// CHECK-NEXT:     "llvm.module_flags"() {{.*}} : () -> ()
// CHECK-NEXT:     "llvm.func"() <{{{.*}}"sym_name" = "fastNTT"{{.*}}}> ({
// CHECK-NEXT:       ^[[bb7:[0-9]+]](%[[varg7_0:[a-zA-Z0-9_]+]] : !llvm.ptr, %[[varg7_1:[a-zA-Z0-9_]+]] : i64, %[[varg7_2:[a-zA-Z0-9_]+]] : i64, %[[varg7_3:[a-zA-Z0-9_]+]] : !llvm.ptr, %[[varg7_4:[a-zA-Z0-9_]+]] : i64, %[[varg7_5:[a-zA-Z0-9_]+]] : i64):
// CHECK-NEXT:         %[[v384:[0-9]+]] = "riscv.li"() <{"value" = 0 : i64}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v382:[0-9]+]] = "riscv.li"() <{"value" = 2 : i64}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v380:[0-9]+]] = "riscv.li"() <{"value" = 1 : i64}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v374:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg7_4]]) : (i64) -> !riscv.reg
// CHECK-NEXT:         %[[v376:[0-9]+]] = "riscv.xor"(%[[v384]], %[[v374]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v377:[0-9]+]] = "riscv.li"() <{"value" = 0 : i64}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v378:[0-9]+]] = "riscv.sltu"(%[[v377]], %[[v376]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v379:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v378]]) : (!riscv.reg) -> i1
// CHECK-NEXT:         %[[v174:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v379]]) : (i1) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.bnez"(%[[v174]]) [^[[bb12:[0-9]+]], ^[[bb13:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb12]]():
// CHECK-NEXT:         %[[v178:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg7_1]]) : (i64) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v178]]) [^[[bb15:[0-9]+]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb13]]():
// CHECK-NEXT:         "riscv_cf.branch"(%[[v382]]) [^[[bb15]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb15]](%[[varg15_0:[a-zA-Z0-9_]+]] : !riscv.reg):
// CHECK-NEXT:         %[[v368:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg7_4]]) : (i64) -> !riscv.reg
// CHECK-NEXT:         %[[v370:[0-9]+]] = "riscv.xor"(%[[v384]], %[[v368]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v371:[0-9]+]] = "riscv.li"() <{"value" = 0 : i64}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v372:[0-9]+]] = "riscv.sltu"(%[[v371]], %[[v370]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v373:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v372]]) : (!riscv.reg) -> i1
// CHECK-NEXT:         %[[v182:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v373]]) : (i1) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.bnez"(%[[v182]]) [^[[bb19:[0-9]+]], ^[[bb20:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb19]]():
// CHECK-NEXT:         "riscv_cf.branch"(%[[v380]]) [^[[bb22:[0-9]+]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb20]]():
// CHECK-NEXT:         %[[v168:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg7_5]]) : (i64) -> !riscv.reg
// CHECK-NEXT:         %[[v386:[0-9]+]] = "riscv.srli"(%[[v168]]) <{"value" = 63 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v171:[0-9]+]] = "riscv.add"(%[[v168]], %[[v386]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v172:[0-9]+]] = "riscv.srai"(%[[v171]]) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v172]]) [^[[bb22]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb22]](%[[varg22_0:[a-zA-Z0-9_]+]] : !riscv.reg):
// CHECK-NEXT:         %[[v162:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg7_1]]) : (i64) -> !riscv.reg
// CHECK-NEXT:         %[[v387:[0-9]+]] = "riscv.srli"(%[[v162]]) <{"value" = 63 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v165:[0-9]+]] = "riscv.add"(%[[v162]], %[[v387]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v166:[0-9]+]] = "riscv.srai"(%[[v165]]) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[varg22_0]], %[[v166]], %[[v384]], %[[varg15_0]]) [^[[bb27:[0-9]+]]] : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb27]](%[[varg27_0:[a-zA-Z0-9_]+]] : !riscv.reg, %[[varg27_1:[a-zA-Z0-9_]+]] : !riscv.reg, %[[varg27_2:[a-zA-Z0-9_]+]] : !riscv.reg, %[[varg27_3:[a-zA-Z0-9_]+]] : !riscv.reg):
// CHECK-NEXT:         %[[v210:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg7_1]]) : (i64) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v384]], %[[v210]]) [^[[bb29:[0-9]+]]] : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb29]](%[[varg29_0:[a-zA-Z0-9_]+]] : !riscv.reg, %[[varg29_1:[a-zA-Z0-9_]+]] : !riscv.reg):
// CHECK-NEXT:         %[[v366:[0-9]+]] = "riscv.slt"(%[[v380]], %[[varg29_1]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v367:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v366]]) : (!riscv.reg) -> i1
// CHECK-NEXT:         %[[v219:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v367]]) : (i1) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.bnez"(%[[v219]]) [^[[bb32:[0-9]+]], ^[[bb33:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb32]]():
// CHECK-NEXT:         %[[v160:[0-9]+]] = "riscv.srai"(%[[varg29_1]]) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v157:[0-9]+]] = "riscv.addi"(%[[varg29_0]]) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v157]], %[[v160]]) [^[[bb29]]] : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb33]]():
// CHECK-NEXT:         %[[v362:[0-9]+]] = "riscv.slt"(%[[varg27_2]], %[[varg29_0]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v363:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v362]]) : (!riscv.reg) -> i1
// CHECK-NEXT:         %[[v228:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v363]]) : (i1) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.bnez"(%[[v228]]) [^[[bb39:[0-9]+]], ^[[bb40:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb39]]():
// CHECK-NEXT:         "riscv_cf.branch"(%[[v384]]) [^[[bb42:[0-9]+]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb42]](%[[varg42_0:[a-zA-Z0-9_]+]] : !riscv.reg):
// CHECK-NEXT:         %[[v356:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg7_1]]) : (i64) -> !riscv.reg
// CHECK-NEXT:         %[[v358:[0-9]+]] = "riscv.div"(%[[v356]], %[[varg27_3]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v354:[0-9]+]] = "riscv.slt"(%[[varg42_0]], %[[v358]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v355:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v354]]) : (!riscv.reg) -> i1
// CHECK-NEXT:         %[[v236:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v355]]) : (i1) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.bnez"(%[[v236]]) [^[[bb46:[0-9]+]], ^[[bb47:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb46]]():
// CHECK-NEXT:         "riscv_cf.branch"(%[[v384]]) [^[[bb49:[0-9]+]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb49]](%[[varg49_0:[a-zA-Z0-9_]+]] : !riscv.reg):
// CHECK-NEXT:         %[[v388:[0-9]+]] = "riscv.srli"(%[[varg27_3]]) <{"value" = 63 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v153:[0-9]+]] = "riscv.add"(%[[varg27_3]], %[[v388]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v154:[0-9]+]] = "riscv.srai"(%[[v153]]) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v350:[0-9]+]] = "riscv.slt"(%[[varg49_0]], %[[v154]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v351:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v350]]) : (!riscv.reg) -> i1
// CHECK-NEXT:         %[[v243:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v351]]) : (i1) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.bnez"(%[[v243]]) [^[[bb53:[0-9]+]], ^[[bb54:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb53]]():
// CHECK-NEXT:         %[[v346:[0-9]+]] = "riscv.mul"(%[[varg27_3]], %[[varg42_0]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v342:[0-9]+]] = "riscv.add"(%[[varg49_0]], %[[v346]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v336:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg7_0]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v338:[0-9]+]] = "riscv.sh3add"(%[[v342]], %[[v336]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v334:[0-9]+]] = "riscv.ld"(%[[v338]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v389:[0-9]+]] = "riscv.srli"(%[[varg27_3]]) <{"value" = 63 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v147:[0-9]+]] = "riscv.add"(%[[varg27_3]], %[[v389]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v148:[0-9]+]] = "riscv.srai"(%[[v147]]) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v331:[0-9]+]] = "riscv.add"(%[[v148]], %[[v342]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v325:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg7_0]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v327:[0-9]+]] = "riscv.sh3add"(%[[v331]], %[[v325]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v323:[0-9]+]] = "riscv.ld"(%[[v327]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v320:[0-9]+]] = "riscv.mul"(%[[varg49_0]], %[[v382]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v142:[0-9]+]] = "riscv.addi"(%[[v320]]) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v316:[0-9]+]] = "riscv.mul"(%[[varg27_1]], %[[v142]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v310:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg7_3]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v312:[0-9]+]] = "riscv.sh3add"(%[[v316]], %[[v310]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v308:[0-9]+]] = "riscv.ld"(%[[v312]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v305:[0-9]+]] = "riscv.mul"(%[[v323]], %[[v308]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v300:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg7_2]]) : (i64) -> !riscv.reg
// CHECK-NEXT:         %[[v301:[0-9]+]] = "riscv.rem"(%[[v305]], %[[v300]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v297:[0-9]+]] = "riscv.add"(%[[v301]], %[[v334]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v292:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg7_2]]) : (i64) -> !riscv.reg
// CHECK-NEXT:         %[[v293:[0-9]+]] = "riscv.rem"(%[[v297]], %[[v292]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v289:[0-9]+]] = "riscv.sub"(%[[v334]], %[[v301]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v284:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg7_2]]) : (i64) -> !riscv.reg
// CHECK-NEXT:         %[[v285:[0-9]+]] = "riscv.add"(%[[v284]], %[[v289]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v280:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg7_2]]) : (i64) -> !riscv.reg
// CHECK-NEXT:         %[[v281:[0-9]+]] = "riscv.rem"(%[[v285]], %[[v280]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v275:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg7_0]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v277:[0-9]+]] = "riscv.sh3add"(%[[v342]], %[[v275]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         "riscv.sd"(%[[v277]], %[[v293]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %[[v268:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg7_0]]) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT:         %[[v270:[0-9]+]] = "riscv.sh3add"(%[[v331]], %[[v268]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         "riscv.sd"(%[[v270]], %[[v281]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         "riscv_cf.branch"() [^[[bb80:[0-9]+]]] : () -> ()
// CHECK-NEXT:       ^[[bb80]]():
// CHECK-NEXT:         %[[v139:[0-9]+]] = "riscv.addi"(%[[varg49_0]]) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v139]]) [^[[bb49]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb54]]():
// CHECK-NEXT:         "riscv_cf.branch"() [^[[bb84:[0-9]+]]] : () -> ()
// CHECK-NEXT:       ^[[bb84]]():
// CHECK-NEXT:         %[[v136:[0-9]+]] = "riscv.addi"(%[[varg42_0]]) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v136]]) [^[[bb42]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb47]]():
// CHECK-NEXT:         %[[v390:[0-9]+]] = "riscv.srli"(%[[varg27_1]]) <{"value" = 63 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v132:[0-9]+]] = "riscv.add"(%[[varg27_1]], %[[v390]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v133:[0-9]+]] = "riscv.srai"(%[[v132]]) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v259:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg7_4]]) : (i64) -> !riscv.reg
// CHECK-NEXT:         %[[v261:[0-9]+]] = "riscv.xor"(%[[v384]], %[[v259]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v262:[0-9]+]] = "riscv.li"() <{"value" = 0 : i64}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v263:[0-9]+]] = "riscv.sltu"(%[[v262]], %[[v261]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v264:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v263]]) : (!riscv.reg) -> i1
// CHECK-NEXT:         %[[v190:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v264]]) : (i1) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.bnez"(%[[v190]]) [^[[bb90:[0-9]+]], ^[[bb91:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb90]]():
// CHECK-NEXT:         %[[v391:[0-9]+]] = "riscv.srli"(%[[varg27_3]]) <{"value" = 63 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v126:[0-9]+]] = "riscv.add"(%[[varg27_3]], %[[v391]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v127:[0-9]+]] = "riscv.srai"(%[[v126]]) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v127]]) [^[[bb94:[0-9]+]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb91]]():
// CHECK-NEXT:         %[[v257:[0-9]+]] = "riscv.add"(%[[varg27_3]], %[[varg27_3]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v257]]) [^[[bb94]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb94]](%[[varg94_0:[a-zA-Z0-9_]+]] : !riscv.reg):
// CHECK-NEXT:         %[[v249:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[varg7_4]]) : (i64) -> !riscv.reg
// CHECK-NEXT:         %[[v251:[0-9]+]] = "riscv.xor"(%[[v384]], %[[v249]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v252:[0-9]+]] = "riscv.li"() <{"value" = 0 : i64}> : () -> !riscv.reg
// CHECK-NEXT:         %[[v253:[0-9]+]] = "riscv.sltu"(%[[v252]], %[[v251]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v254:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v253]]) : (!riscv.reg) -> i1
// CHECK-NEXT:         %[[v221:[0-9]+]] = "builtin.unrealized_conversion_cast"(%[[v254]]) : (i1) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.bnez"(%[[v221]]) [^[[bb99:[0-9]+]], ^[[bb100:[0-9]+]]] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb99]]():
// CHECK-NEXT:         %[[v247:[0-9]+]] = "riscv.add"(%[[varg27_0]], %[[varg27_0]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v247]]) [^[[bb103:[0-9]+]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb100]]():
// CHECK-NEXT:         %[[v392:[0-9]+]] = "riscv.srli"(%[[varg27_0]]) <{"value" = 63 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v120:[0-9]+]] = "riscv.add"(%[[varg27_0]], %[[v392]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %[[v121:[0-9]+]] = "riscv.srai"(%[[v120]]) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[v121]]) [^[[bb103]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb103]](%[[varg103_0:[a-zA-Z0-9_]+]] : !riscv.reg):
// CHECK-NEXT:         "riscv_cf.branch"() [^[[bb107:[0-9]+]]] : () -> ()
// CHECK-NEXT:       ^[[bb107]]():
// CHECK-NEXT:         %[[v115:[0-9]+]] = "riscv.addi"(%[[varg27_2]]) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         "riscv_cf.branch"(%[[varg103_0]], %[[v133]], %[[v115]], %[[varg94_0]]) [^[[bb27]]] : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:       ^[[bb40]]():
// CHECK-NEXT:         "llvm.return"() : () -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) {{.*}} : () -> ()
