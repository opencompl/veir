// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
    ^bb0():
      %0 = "riscv.li"() <{ "value" = 13 : i64 }>  : () -> !riscv.reg
      %1 = "riscv.li"() <{ "value" = 17 : i64 }> : () -> !riscv.reg
      // Immediate load 
      %2 = "riscv.lui"() <{"value" = 13 : i20}> : () -> !riscv.reg
      %3 = "riscv.auipc"(%0) <{"value" = 13 : i20}> : (!riscv.reg) -> !riscv.reg
      // Immediate operations 
      %4 = "riscv.addi"(%0) <{"value" = 5 : i12}> : (!riscv.reg) -> !riscv.reg
      %5 = "riscv.slti"(%0) <{"value" = 7 : i12}> : (!riscv.reg) -> !riscv.reg
      %6 = "riscv.sltiu"(%0) <{"value" = 11 : i12}> : (!riscv.reg) -> !riscv.reg
      %7 = "riscv.andi"(%0) <{"value" = 13 : i12}> : (!riscv.reg) -> !riscv.reg
      %8 = "riscv.ori"(%0) <{"value" = 17 : i12}> : (!riscv.reg) -> !riscv.reg
      %9 = "riscv.xori"(%0) <{"value" = 23 : i12}> : (!riscv.reg) -> !riscv.reg
      %10 = "riscv.addiw"(%0) <{"value" = 29 : i12}> : (!riscv.reg) -> !riscv.reg
      %11 = "riscv.slli"(%0) <{"value" = 31 : i6}> : (!riscv.reg) -> !riscv.reg
      %12 = "riscv.srli"(%0) <{"value" = 33 : i6}> : (!riscv.reg) -> !riscv.reg
      %13 = "riscv.srai"(%0) <{"value" = 37 : i6}> : (!riscv.reg) -> !riscv.reg
      %14 = "riscv.slliw"(%0) <{ "value" = 13 : i5 }> : (!riscv.reg) -> !riscv.reg
      %15 = "riscv.srliw"(%0) <{ "value" = 17 : i5 }> : (!riscv.reg) -> !riscv.reg
      %16 = "riscv.sraiw"(%0) <{ "value" = 19 : i5 }> : (!riscv.reg) -> !riscv.reg
      %17 = "riscv.slliuw"(%0) <{"value" = 13 : i6 }> : (!riscv.reg) -> !riscv.reg
      %18 = "riscv.roriw"(%0) <{"value" = 13 : i5 }> : (!riscv.reg) -> !riscv.reg
      %19 = "riscv.rori"(%0) <{"value" = 13 : i6 }> : (!riscv.reg) -> !riscv.reg
      %20 = "riscv.bclri"(%0) <{"value" = 13 : i6}> : (!riscv.reg) -> !riscv.reg
      %21 = "riscv.bexti"(%0) <{"value" = 13 : i6}> : (!riscv.reg) -> !riscv.reg
      %22 = "riscv.binvi"(%0) <{"value" = 13 : i6}> : (!riscv.reg) -> !riscv.reg
      %23 = "riscv.bseti"(%0) <{"value" = 13 : i6}> : (!riscv.reg) -> !riscv.reg
      // Unary operations 
      %24 = "riscv.sextb"(%0) : (!riscv.reg) -> !riscv.reg
      %25 = "riscv.sexth"(%0) : (!riscv.reg) -> !riscv.reg
      %26 = "riscv.zexth"(%0) : (!riscv.reg) -> !riscv.reg
      %27 = "riscv.clz"(%0) : (!riscv.reg) -> !riscv.reg
      %28 = "riscv.clzw"(%0) : (!riscv.reg) -> !riscv.reg
      %29 = "riscv.ctz"(%0) : (!riscv.reg) -> !riscv.reg
      %30 = "riscv.ctzw"(%0) : (!riscv.reg) -> !riscv.reg
      %cpop = "riscv.cpop"(%0) : (!riscv.reg) -> !riscv.reg
      %cpopw = "riscv.cpopw"(%0) : (!riscv.reg) -> !riscv.reg
      // Binary operations 
      %31 = "riscv.add"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %32 = "riscv.sub"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %33 = "riscv.sll"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %34 = "riscv.slt"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %35 = "riscv.sltu"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %36 = "riscv.xor"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %37 = "riscv.srl"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %38 = "riscv.sra"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %39 = "riscv.or"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %40 = "riscv.and"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %41 = "riscv.addw"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %42 = "riscv.subw"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %43 = "riscv.sllw"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %44 = "riscv.srlw"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %45 = "riscv.sraw"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %46 = "riscv.rem"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %47 = "riscv.remu"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %48 = "riscv.remw"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %49 = "riscv.remuw"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %50 = "riscv.mul"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %51 = "riscv.mulh"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %52 = "riscv.mulhu"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %53 = "riscv.mulhsu"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %54 = "riscv.mulw"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %55 = "riscv.div"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %56 = "riscv.divw"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %57 = "riscv.divu"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %58 = "riscv.divuw"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %59 = "riscv.adduw"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %60 = "riscv.sh1adduw"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %61 = "riscv.sh2adduw"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %62 = "riscv.sh3adduw"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %63 = "riscv.sh1add"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %64 = "riscv.sh2add"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %65 = "riscv.sh3add"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %66 = "riscv.andn"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %67 = "riscv.orn"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %68 = "riscv.xnor"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %69 = "riscv.max"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %70 = "riscv.maxu"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %71 = "riscv.min"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %72 = "riscv.minu"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %73 = "riscv.rol"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %74 = "riscv.ror"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %75 = "riscv.rolw"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %76 = "riscv.rorw"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %77 = "riscv.bclr"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %78 = "riscv.bext"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %79 = "riscv.binv"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %80 = "riscv.bset"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %81 = "riscv.pack"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %82 = "riscv.packh"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %83 = "riscv.packw"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      // Zicond
      %czeqz = "riscv.czeroeqz"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      %cznez = "riscv.czeronez"(%0, %1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      // pseudo instructions
      %84 = "riscv.mv"(%83) : (!riscv.reg) -> !riscv.reg
      %85 = "riscv.not"(%83) : (!riscv.reg) -> !riscv.reg
      %86 = "riscv.neg"(%83) : (!riscv.reg) -> !riscv.reg
      %87 = "riscv.negw"(%83) : (!riscv.reg) -> !riscv.reg
      %88 = "riscv.sextw"(%83) : (!riscv.reg) -> !riscv.reg
      %89 = "riscv.zextb"(%83) : (!riscv.reg) -> !riscv.reg
      %90 = "riscv.zextw"(%83) : (!riscv.reg) -> !riscv.reg
      %91 = "riscv.seqz"(%83) : (!riscv.reg) -> !riscv.reg
      %92 = "riscv.snez"(%83) : (!riscv.reg) -> !riscv.reg
      %93 = "riscv.sltz"(%83) : (!riscv.reg) -> !riscv.reg
      %94 = "riscv.sgtz"(%83) : (!riscv.reg) -> !riscv.reg
      // Memory operations
      %95 = "riscv.ld"(%0) <{"value" = 5 : i12}> : (!riscv.reg) -> !riscv.reg
      %lw = "riscv.lw"(%0) <{"value" = 5 : i12}> : (!riscv.reg) -> !riscv.reg
      %lwu = "riscv.lwu"(%0) <{"value" = 5 : i12}> : (!riscv.reg) -> !riscv.reg
      %lh = "riscv.lh"(%0) <{"value" = 5 : i12}> : (!riscv.reg) -> !riscv.reg
      %lhu = "riscv.lhu"(%0) <{"value" = 5 : i12}> : (!riscv.reg) -> !riscv.reg
      %lb = "riscv.lb"(%0) <{"value" = 5 : i12}> : (!riscv.reg) -> !riscv.reg
      %lbu = "riscv.lbu"(%0) <{"value" = 5 : i12}> : (!riscv.reg) -> !riscv.reg
      "riscv.sd"(%0, %1) <{"value" = 5 : i12}> : (!riscv.reg, !riscv.reg) -> ()
      "riscv.sw"(%0, %1) <{"value" = 5 : i12}> : (!riscv.reg, !riscv.reg) -> ()
      "riscv.sh"(%0, %1) <{"value" = 5 : i12}> : (!riscv.reg, !riscv.reg) -> ()
      "riscv.sb"(%0, %1) <{"value" = 5 : i12}> : (!riscv.reg, !riscv.reg) -> ()
      "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "func.func"() <{"function_type" = () -> (), "sym_name" = "main"}> ({
// CHECK-NEXT:       ^{{.*}}():
// CHECK-NEXT:         %{{.*}} = "riscv.li"() <{"value" = 13 : i64}> : () -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.li"() <{"value" = 17 : i64}> : () -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.lui"() <{"value" = 13 : i20}> : () -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.auipc"(%{{.*}}) <{"value" = 13 : i20}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.addi"(%{{.*}}) <{"value" = 5 : i12}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.slti"(%{{.*}}) <{"value" = 7 : i12}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.sltiu"(%{{.*}}) <{"value" = 11 : i12}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.andi"(%{{.*}}) <{"value" = 13 : i12}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.ori"(%{{.*}}) <{"value" = 17 : i12}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.xori"(%{{.*}}) <{"value" = 23 : i12}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.addiw"(%{{.*}}) <{"value" = 29 : i12}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.slli"(%{{.*}}) <{"value" = 31 : i6}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.srli"(%{{.*}}) <{"value" = 33 : i6}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.srai"(%{{.*}}) <{"value" = 37 : i6}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.slliw"(%{{.*}}) <{"value" = 13 : i5}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.srliw"(%{{.*}}) <{"value" = 17 : i5}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.sraiw"(%{{.*}}) <{"value" = 19 : i5}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.slliuw"(%{{.*}}) <{"value" = 13 : i6}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.roriw"(%{{.*}}) <{"value" = 13 : i5}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.rori"(%{{.*}}) <{"value" = 13 : i6}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.bclri"(%{{.*}}) <{"value" = 13 : i6}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.bexti"(%{{.*}}) <{"value" = 13 : i6}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.binvi"(%{{.*}}) <{"value" = 13 : i6}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.bseti"(%{{.*}}) <{"value" = 13 : i6}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.sextb"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.sexth"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.zexth"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.clz"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.clzw"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.ctz"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.ctzw"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.cpop"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.cpopw"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.add"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.sub"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.sll"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.slt"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.sltu"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.xor"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.srl"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.sra"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.or"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.and"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.addw"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.subw"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.sllw"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.srlw"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.sraw"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.rem"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.remu"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.remw"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.remuw"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.mul"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.mulh"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.mulhu"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.mulhsu"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.mulw"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.div"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.divw"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.divu"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.divuw"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.adduw"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.sh1adduw"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.sh2adduw"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.sh3adduw"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.sh1add"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.sh2add"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.sh3add"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.andn"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.orn"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.xnor"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.max"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.maxu"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.min"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.minu"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.rol"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.ror"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.rolw"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.rorw"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.bclr"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.bext"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.binv"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.bset"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.pack"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.packh"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.packw"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.czeroeqz"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.czeronez"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.mv"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.not"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.neg"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.negw"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.sextw"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.zextb"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.zextw"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.seqz"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.snez"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.sltz"(%{{.*}}) : (!riscv.reg) -> !riscv.reg 
// CHECK-NEXT:         %{{.*}} = "riscv.sgtz"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.ld"(%{{.*}}) <{"value" = 5 : i12}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.lw"(%{{.*}}) <{"value" = 5 : i12}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.lwu"(%{{.*}}) <{"value" = 5 : i12}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.lh"(%{{.*}}) <{"value" = 5 : i12}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.lhu"(%{{.*}}) <{"value" = 5 : i12}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.lb"(%{{.*}}) <{"value" = 5 : i12}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.lbu"(%{{.*}}) <{"value" = 5 : i12}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         "riscv.sd"(%{{.*}}, %{{.*}}) <{"value" = 5 : i12}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         "riscv.sw"(%{{.*}}, %{{.*}}) <{"value" = 5 : i12}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         "riscv.sh"(%{{.*}}, %{{.*}}) <{"value" = 5 : i12}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         "riscv.sb"(%{{.*}}, %{{.*}}) <{"value" = 5 : i12}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         "func.return"() : () -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) : () -> ()
