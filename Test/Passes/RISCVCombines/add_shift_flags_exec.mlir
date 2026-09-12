// RUN: veir-interpret %s | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=riscv-combine > %t
// RUN: veir-interpret %t | filecheck %s

// Block arguments keep both add_shift operand orders reachable. Neither the
// negation's nor the shift's overflow flags apply to their replacements.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8, i8, i8, i8, i8)}> ({
    %min = "llvm.mlir.constant"() <{value = -128 : i8}> : () -> i8
    %one = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    %minusOne = "llvm.mlir.constant"() <{value = -1 : i8}> : () -> i8
    %zero = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    "cf.br"(%min, %one, %minusOne, %zero) [^test] : (i8, i8, i8, i8) -> ()
  ^test(%a: i8, %b: i8, %negative: i8, %z: i8):
    %wrappedZero = "llvm.mlir.constant"() <{value = 256 : i16}> : () -> i8
    %amount = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    %seven = "llvm.mlir.constant"() <{value = 7 : i8}> : () -> i8

    // 0 - 1 is defined with nsw; -128 - (1 << 1) overflows signed arithmetic.
    %neg = "llvm.sub"(%wrappedZero, %b) <{overflowFlags = 1 : i32}> : (i8, i8) -> i8
    %shift = "llvm.shl"(%neg, %amount) : (i8, i8) -> i8
    %subNsw = "llvm.add"(%a, %shift) : (i8, i8) -> i8
    %subNswCommute = "llvm.add"(%shift, %a) : (i8, i8) -> i8

    // -1 << 7 is defined with nsw, but 1 << 7 overflows signed arithmetic.
    %signedShift = "llvm.shl"(%neg, %seven) <{overflowFlags = 1 : i32}> : (i8, i8) -> i8
    %shiftNsw = "llvm.add"(%z, %signedShift) : (i8, i8) -> i8
    %shiftNswCommute = "llvm.add"(%signedShift, %z) : (i8, i8) -> i8

    // 1 << 1 is defined with nuw, but the replacement 255 << 1 overflows.
    %positive = "llvm.sub"(%wrappedZero, %negative) : (i8, i8) -> i8
    %unsignedShift = "llvm.shl"(%positive, %amount) <{overflowFlags = 2 : i32}> : (i8, i8) -> i8
    %shiftNuw = "llvm.add"(%z, %unsignedShift) : (i8, i8) -> i8
    %shiftNuwCommute = "llvm.add"(%unsignedShift, %z) : (i8, i8) -> i8
    "func.return"(%subNsw, %subNswCommute, %shiftNsw, %shiftNswCommute, %shiftNuw, %shiftNuwCommute) : (i8, i8, i8, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x7e#8, 0x7e#8, 0x80#8, 0x80#8, 0x02#8, 0x02#8]
