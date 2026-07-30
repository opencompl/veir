// REQUIRES: clang, mlir-translate, mlir-opt
// RUN: split-file %s %t
// RUN: veir-opt %t/input.mlir -p=mod-arith,arith-to-llvm | mlir-opt --convert-func-to-llvm | mlir-translate --mlir-to-llvmir -o %t/kernel.ll
// RUN: clang -Wno-override-module %t/driver.c %t/kernel.ll -o %t/test
// RUN: %t/test | filecheck %s

// CHECK: OK

//--- input.mlir
"builtin.module"() ({
  "func.func"() <{function_type = (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>, sym_name = "mod_arith_chain"}> ({
  ^bb0(%a : !mod_arith.int<12289 : i32>, %b : !mod_arith.int<12289 : i32>):
    %c5 = "mod_arith.constant"() <{"value" = 5 : i32}> : () -> !mod_arith.int<12289 : i32>
    %s = "mod_arith.add"(%a, %b) : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    %d = "mod_arith.sub"(%a, %b) : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    %m = "mod_arith.mul"(%s, %d) : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    %r = "mod_arith.mul"(%m, %c5) : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    %out = "mod_arith.add"(%r, %a) : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    "func.return"(%out) : (!mod_arith.int<12289 : i32>) -> ()
  }) : () -> ()
}) : () -> ()

//--- driver.c
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

uint32_t mod_arith_chain(uint32_t, uint32_t);

static uint32_t reference(uint32_t a, uint32_t b) {
  const uint32_t q = 12289;
  uint64_t sum = ((uint64_t)a + (uint64_t)b) % q;
  uint64_t difference = ((uint64_t)a + q - (uint64_t)b) % q;
  uint64_t product = sum * difference % q;
  uint64_t scaled = product * 5 % q;
  uint64_t result = (scaled + a) % q;
  return (uint32_t)result;
}

int main(void) {
  const uint32_t q = 12289;
  const unsigned int seed = 0;
  const uint32_t number_of_tests = 16384;
  srand(seed);
  for (uint32_t i = 0; i < number_of_tests; ++i) {
    uint32_t a = (uint32_t)rand() % q;
    uint32_t b = (uint32_t)rand() % q;
    uint32_t got = mod_arith_chain(a, b);
    uint32_t expected = reference(a, b);
    if (got != expected) {
      printf("FAIL mod_arith_chain(%u, %u) = %u, expected %u\n",
             a, b, got, expected);
      return 1;
    }
  }
  printf("OK\n");
  return 0;
}
