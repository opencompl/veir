// RUN: ./Tools/vcc --emit-mlir -O %s -o - | filecheck %s
// RUN: ./Tools/vcc -c %s -o %t.o
// RUN: test -s %t.o
// RUN: ./Tools/vcc -S %s -o %t.s
// RUN: test -s %t.s

/* 
    This file contains a very naive implementation of the FastNTT algorithm. 
    It is an example of a real application we should aim to lower with out RISC-V instruction 
    selection. It is also interesting in the vector-extension perspective, 
    which significantly optimizes it. 
    Some references: 
    - https://ieeexplore.ieee.org/document/10177902 
    - https://eprint.iacr.org/2024/585.pdf
    - https://link.springer.com/chapter/10.1007/978-3-031-46077-7_22 
    - https://fprox.substack.com/p/faster-ntt-with-risc-v-vector 
    
    Our implementation is based on the description in HEIR : 
        def fastNTT(coeffs, n, cmod, roots, inverse):
         m = inverse ? n : 2             # m denotes the batchSize or stride
         r = inverse ? 1 : degree / 2    # r denotes the exponent of the root
         for (s = 0; s < log2(n); s++):
           for (k = 0; k < n / m; k++):
             for (j = 0; j < m / 2; j++):
               A = coeffs[k * m + j]
               B = coeffs[k * m + j + m / 2]
               root = roots[(2 * j + 1) * rootExp]
               coeffs[k * m + j], coeffs[k * m + j + m / 2]
                 = bflyOp(A, B, root, cmod)
             end
           end
           m = inverse ? m / 2 : m * 2
           r = inverse ? r * 2 : m / 2
         end
        where bflyOp is one of:
        bflyCT(A, B, root, cmod):
            (A + root * B % cmod, A - root * B % cmod)
    
        bflyGS(A, B, root, cmod):
            (A + B % cmod, (A - B) * root % cmod)
    Reference: 
    https://github.com/google/heir/blob/1210ad37dc9531d6e60d8ddbce81dbd79f7626a6/lib/Dialect/Polynomial/Conversions/PolynomialToModArith/PolynomialToModArith.cpp#L1060 
*/
#include <stddef.h>

// log2(0) = 0
// log2(1) = 0
// log2(2*n) = 1 + log2(n)
__attribute__((always_inline)) static long log2FloorAux(long n) {
    long result = 0;
    while (n > 1) {
        n >>= 1;
        result++;
    }
    return result;
}

__attribute__((always_inline)) static long log2Floor(long n) {
    return log2FloorAux(n);
}

/* bflyCT */
__attribute__((always_inline)) static void bflyCT(long A, long B, long root, long cmod, long *outA, long *outB) {
    *outA = (A + root * B % cmod) % cmod;
    *outB = (A - root * B % cmod + cmod) % cmod;
}

/* bflyGS */
__attribute__((always_inline)) static void bflyGS(long A, long B, long root, long cmod, long *outA, long *outB) {
    *outA = (A + B) % cmod;
    *outB = (A - B) * root % cmod;
}

__attribute__((always_inline)) void fastNTT(long *coeffs, long n, long cmod, const long *roots, long inverse, long degree) {
    long m = inverse ? n : 2;
    long r = inverse ? 1 : degree / 2;
    long rootExp = n / 2;

    for (long s = 0; s < log2Floor(n); s++) {
        for (long k = 0; k < n / m; k++) {
            for (long j = 0; j < m / 2; j++) {
                long A    = coeffs[k * m + j];
                long B    = coeffs[k * m + j + m / 2];
                long root = roots[(2 * j + 1) * rootExp];
                long outA, outB;
                bflyCT(A, B, root, cmod, &outA, &outB);
                coeffs[k * m + j]         = outA;
                coeffs[k * m + j + m / 2] = outB;
            }
        }
        rootExp = rootExp / 2;
        m = inverse ? m / 2 : m * 2;
        r = inverse ? r * 2 : r / 2;
    }
}