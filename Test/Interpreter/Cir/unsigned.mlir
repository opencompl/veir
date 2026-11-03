// RUN: veir-opt %s -p=cir > %t.mlir && veir-interpret %t.mlir | filecheck %s

// 200 + 100 wraps to 44 on u8; 255 / 2 = 127 unsigned; (44 | 127) & 0x0f = 15; 15 >> 1 = 7; 7 << 2 = 28.
"builtin.module"() ({
  "cir.func"() <{function_type = !cir.func<() -> !cir.int<u, 8>>, sym_name = "main"}> ({
    %a = "cir.const"() <{value = #cir.int<200> : !cir.int<u, 8>}> : () -> !cir.int<u, 8>
    %b = "cir.const"() <{value = #cir.int<100> : !cir.int<u, 8>}> : () -> !cir.int<u, 8>
    %m = "cir.const"() <{value = #cir.int<255> : !cir.int<u, 8>}> : () -> !cir.int<u, 8>
    %two = "cir.const"() <{value = #cir.int<2> : !cir.int<u, 8>}> : () -> !cir.int<u, 8>
    %mask = "cir.const"() <{value = #cir.int<15> : !cir.int<u, 8>}> : () -> !cir.int<u, 8>
    %one = "cir.const"() <{value = #cir.int<1> : !cir.int<u, 8>}> : () -> !cir.int<u, 8>
    %s = "cir.add"(%a, %b) <{no_signed_wrap = false, no_unsigned_wrap = false, saturated = false}> : (!cir.int<u, 8>, !cir.int<u, 8>) -> !cir.int<u, 8>
    %d = "cir.div"(%m, %two) : (!cir.int<u, 8>, !cir.int<u, 8>) -> !cir.int<u, 8>
    %o = "cir.or"(%s, %d) : (!cir.int<u, 8>, !cir.int<u, 8>) -> !cir.int<u, 8>
    %n = "cir.and"(%o, %mask) : (!cir.int<u, 8>, !cir.int<u, 8>) -> !cir.int<u, 8>
    %r = "cir.shift"(%n, %one) : (!cir.int<u, 8>, !cir.int<u, 8>) -> !cir.int<u, 8>
    %l = "cir.shift"(%r, %two) <{isShiftleft}> : (!cir.int<u, 8>, !cir.int<u, 8>) -> !cir.int<u, 8>
    "cir.return"(%l) : (!cir.int<u, 8>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x1c#8]
