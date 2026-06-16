// RUN: ./Tools/vcc -O --emit-mlir %s -o %t.mlir
// RUN: tbd 
/*
    An implementation of the ChaCha20 stream cipher (RFC 8439, see bellow).
    Some refrences:
    - Algorithm: https://cr.yp.to/chacha.htmlhttps://cr.yp.to/chacha/chacha-20080120.pdf
    - RFC 8439: https://datatracker.ietf.org/doc/html/rfc8439

    The structure (state matrix, quarter-round, double-round etc.) follows the public RFC, analog to
    the reference Python implementation at https://github.com/ph4r05/py-chacha20poly1305 (chacha.py).

    The cipher is built up in three layers, each calling the previous one:
      - quarter_round: the basic mixing step on four state words;
      - chacha20_block: 20 rounds over the 16-word state, producing 64 keystream bytes;
      - chacha20_xor:   full stream encryption of an arbitrary-length message.

    The main function runs the full encryption on the RFC 8439 section 2.4.2 inputs
    and returns the first four ciphertext bytes. 

    (Currently not interpreted/)

*/

#include <stddef.h>
#include <stdint.h>


__attribute__((always_inline)) static uint32_t rotl32(uint32_t x, int n) {
    return (x << n) | (x >> (32 - n));
}

__attribute__((always_inline)) static uint32_t load32le(const uint8_t *p) {
    return (uint32_t)p[0] | ((uint32_t)p[1] << 8) | ((uint32_t)p[2] << 16) | ((uint32_t)p[3] << 24);
}

__attribute__((always_inline)) static void store32le(uint8_t *p, uint32_t v) {
    p[0] = (uint8_t)v;
    p[1] = (uint8_t)(v >> 8);
    p[2] = (uint8_t)(v >> 16);
    p[3] = (uint8_t)(v >> 24);
}

// one ChaCha20 quarter-round on the four state words x[a], x[b], x[c], x[d] (shuffles matrix state)
__attribute__((always_inline)) static void quarter_round(uint32_t x[16], int a, int b, int c, int d) {
    x[a]+= x[b]; x[d]^= x[a]; x[d] = rotl32(x[d],16);
    x[c]+= x[d]; x[b]^= x[c]; x[b] = rotl32(x[b],12);
    x[a]+= x[b]; x[d]^= x[a]; x[d] = rotl32(x[d],8);
    x[c]+= x[d]; x[b]^= x[c]; x[b] = rotl32(x[b],7);
}

// produces one 64-byte ChaCha20 keystream block into out
__attribute__((always_inline)) static void chacha20_block(const uint8_t key[32], uint32_t counter, const uint8_t nonce[12], uint8_t out[64]) {
    uint32_t state[16];
    state[0] = 0x61707865; // these constants are the ASCII codes of "expand 32-byte k" and fixed in the algo.
    state[1] = 0x3320646e;
    state[2] = 0x79622d32;
    state[3] = 0x6b206574;
    for (int i = 0; i < 8; i++)
        state[4+i] = load32le(key + 4*i);
    state[12] = counter;
    for (int i = 0; i < 3; i++)
        state[13+i] = load32le(nonce + 4*i);

    uint32_t x[16];
    for (int i = 0; i < 16; i++)
        x[i] = state[i];

    // 20 rounds (10 double rounds each 4 col. rounds then four diag.rounds)
    for (int i = 0; i < 10; i++) {
        quarter_round(x,0,4,8,12);
        quarter_round(x,1,5,9,13);
        quarter_round(x,2,6,10,14);
        quarter_round(x,3,7,11,15);
        quarter_round(x,0,5,10,15);
        quarter_round(x,1,6,11,12);
        quarter_round(x,2,7,8,13);
        quarter_round(x,3,4,9,14);
    }

    for (int i = 0; i < 16; i++)
        store32le(out + 4*i, x[i]+ state[i]);
}

// Encrypt/decrypt len bytes starting from block counter
__attribute__((always_inline)) static inline void chacha20_xor(const uint8_t key[32], const uint8_t nonce[12], uint32_t counter, const uint8_t *in, uint8_t *out, size_t len) {
    uint8_t block[64];
    size_t done = 0;
    while (done < len) {
        chacha20_block(key, counter, nonce, block);
        counter++;
        size_t chunk = len - done;
        if (chunk > 64)
            chunk = 64;
        for (size_t i = 0; i < chunk; i++)
            out[done+i] = in[done+i] ^ block[i];
        done += chunk;
    }
}

int main() {
    uint8_t key[32];
    for (int i = 0; i < 32; i++)
        key[i] = (uint8_t)i;

    uint8_t nonce[12] = {0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                         0x00, 0x4a, 0x00, 0x00, 0x00, 0x00};
    
                         const char *msg = "Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.";
    
    uint8_t plaintext[114];
    for (int i = 0; i < 114; i++)
        plaintext[i] = (uint8_t)msg[i];

    uint8_t ciphertext[114];
    chacha20_xor(key, nonce, 1, plaintext, ciphertext, 114);

    // Return the first four ciphertext bytes (so basically the start of the first block) which we will check against the RFC 8439 expected value (0x6e2e359a).
    // Currently "restricted" to return only the first four bytes to obtain a 32bit value.
    return ((int)ciphertext[0] << 24) | ((int)ciphertext[1] << 16) | ((int)ciphertext[2] << 8) | (int)ciphertext[3];
}

// CHECK: Program output: #[0x6e2e359a#32] (CURRENTLY NOT USED BUT WOULD BE THE VALUE TO CHECK AGAINST THE RFC EXPECTED OUTPUT WHEN INTERPRETATION WORKS) 