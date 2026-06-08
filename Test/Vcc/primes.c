// RUN: ./Tools/vcc -O --emit-mlir %s -o %t.mlir
// RUN: veir-interpret %t.mlir | filecheck %s

int main(void) {
    int count = 0;
    int n = 2;
    int last_prime = 0;

    while (count < 10) {
        int prime = 1;

        for (int i = 2; i * i <= n; i++) {
            if (n % i == 0) {
                prime = 0;
                break;
            }
        }

        if (prime) {
            last_prime = n;
            count++;
        }

        n++;
    }

    // main's return value is 29, the 10th prime number
    return last_prime;
}

// CHECK: Program output: #[0x0000001d#32]
