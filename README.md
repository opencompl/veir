# Verified Intermediate Representation

VeIR is a compiler infrastructure written in Lean that offers both an
[MLIR](https://mlir.llvm.org/)-style imperative design and
(optional) ITP-level verification.
VeIR connects with MLIR via the MLIR textual format, making it
easy to combine MLIR and VeIR tools.

| VeIR Features                                         | Complete   | Verified |
|-------------------------------------------------------|------------| ---------|
| MLIR core data structures (block, operation, region)  | ✅         | 🔒        |
| define dialects                                       | ✅ (basic) |           |
| pass infrastructure                                   | ✅         |           |
| peephole rewriter                                     | ✅         |           |
| peephole rewriter (declarative)                       |            |           |
| interpreter framework                                 | ✅         |           |

## Building and testing

Building VeIR requires [Lean 4 and its build tool Lake](https://lean-lang.org/install/).

Common tasks are wrapped in the [`Makefile`](Makefile): `make build` to build and
`make tests` to run the tests. Run `make` to list every target.

Lake builds ExArray's native C code with Lean's bundled LLVM toolchain.
Non-Nix builds need GMP development headers and `pkg-config` (or `pkgconf`).

With Nix, `nix develop` enters a development shell containing Lean's toolchain
manager and all native and Python dependencies needed by those Make targets.
Executable targets like `veir-opt` and `veir-interpret` can be run with `nix run
.#veir-opt`, `nix run .#veir-interpret`, etc. For convenience, makefile targets
are also exposed as flake apps with `nix run .#build` and `nix run .#tests`;
`nix run .` displays the Makefile help.
If both [`direnv`](https://direnv.net) and Nix are installed, run `direnv allow`
to automatically activate the development shell whenever you enter the project
directory.

Our testing framework is split into two parts: unit tests written in Lean and
[FileCheck](https://llvm.org/docs/CommandGuide/FileCheck.html) tests for the
command line tool `veir-opt`. The FileCheck tests require
[uv](https://docs.astral.sh/uv/) to be installed.

Run a single benchmark with `lake exe run-benchmarks <name>` (see
[`Veir/Benchmarks.lean`](Veir/Benchmarks.lean) for the available names).

## From C to VeIR

This section gives an example showing how to run code through a VeIR
pass, starting from C code.

Prerequisite: An up-to-date MLIR bin directory in your PATH.

Start with a C function:
```bash
cat << _end_ > demorgan.c
unsigned d1(unsigned p, unsigned q) {
  return ~(~p & ~q);
}

unsigned short d2(unsigned short p, unsigned short q) {
  return ~(~p | ~q);
}
_end_
```

Compile to LLVM IR:
```bash
clang -cc1 -O0 -disable-O0-optnone -emit-llvm demorgan.c
```

Optimize it a little:
```bash
opt -passes=sroa demorgan.ll -S -o demorgan-opt.ll
```

Translate to MLIR:
```bash
mlir-translate --import-llvm demorgan-opt.ll | mlir-opt --mlir-print-op-generic --mlir-print-local-scope > demorgan-opt.mlir
```

Optimize using VeIR's InstCombine and DCE (dead code elimination) passes:
```bash
lake exec veir-opt -p=instcombine,dce demorgan-opt.mlir
```

Alternatively, you can batch up these commands using the provided
compiler driver and emit the optimized MLIR to stdout:
```bash
Tools/vcc demorgan.c --emit-mlir -O -o -
```

Without an explicit emit mode, `vcc` translates VeIR's output back to
LLVM IR and asks `clang` to produce an executable:
```bash
cat << _end_ > hello.c
#include <stdio.h>

int main(void) {
  printf("hello, world\n");
}
_end_

Tools/vcc hello.c -o hello
```

## Setting up a RISC-V user-mode environment

VeIR's RISC-V backend is tested by running 64-bit RISC-V Linux executables
under QEMU's user-mode emulator, `qemu-riscv64`. The setup below also gives
you a riscv64 cross toolchain for compiling and debugging your own programs.

### Linux

On Debian or Ubuntu, install the cross toolchain and user-mode QEMU:
```bash
sudo apt-get install -y \
  gcc-riscv64-linux-gnu g++-riscv64-linux-gnu libc6-dev-riscv64-cross \
  qemu-user qemu-user-binfmt gdb-multiarch clang lld
```

`qemu-user-binfmt` registers QEMU with the kernel so that riscv64 executables
can be run directly. Dynamically linked executables also need to find the
riscv64 C library:
```bash
export QEMU_LD_PREFIX=/usr/riscv64-linux-gnu
```

### macOS

`qemu-riscv64` only runs on Linux hosts, so on macOS the emulator runs inside a
small Linux VM managed by [Lima](https://lima-vm.io). Create a VM named `rv64`
(this is the name `vsmith` looks for). Your home directory is mounted in the VM
at the same path:
```bash
brew install lima
limactl start --name=rv64 --vm-type=vz --mount-writable template:ubuntu-24.04
```

Then install the packages from the Linux section inside the VM and set
`QEMU_LD_PREFIX` in the VM's shell profile:
```bash
limactl shell rv64 sudo apt-get update
limactl shell rv64 sudo apt-get install -y \
  gcc-riscv64-linux-gnu g++-riscv64-linux-gnu libc6-dev-riscv64-cross \
  qemu-user qemu-user-binfmt gdb-multiarch clang lld
limactl shell rv64 sh -c \
  "echo 'export QEMU_LD_PREFIX=/usr/riscv64-linux-gnu' >> ~/.bashrc"
```

Use `limactl shell rv64` to open a shell in the VM, or `limactl shell rv64
<command>` to run a single command. `limactl stop rv64` and `limactl start
rv64` stop and restart it.

### Checking the setup

On Linux, or in a shell inside the VM on macOS:
```bash
riscv64-linux-gnu-gcc -O2 hello.c -o hello-rv && ./hello-rv
riscv64-linux-gnu-gcc -O2 -static hello.c -o hello-rv-static && ./hello-rv-static
clang --target=riscv64-linux-gnu -O2 hello.c -o hello-clang && ./hello-clang
```

To debug a program, start it under QEMU's GDB stub and attach `gdb-multiarch`:
```bash
qemu-riscv64 -g 1234 ./hello-rv-static &
gdb-multiarch -ex 'set architecture riscv:rv64' -ex 'target remote :1234' ./hello-rv-static
```

## Running vsmith in RISC-V mode

[`Tools/vsmith`](Tools/vsmith) is a differential fuzzer: it generates random
programs and checks that `veir-interpret` gives the same result before and after
optimization. With `--riscv` it runs the RISC-V pipeline instead, and it also
lowers each optimized program to LLVM MIR, compiles it into a static riscv64
Linux executable, runs it under `qemu-riscv64`, and checks that the value it
returns matches the interpreter's:
```bash
lake build
Tools/vsmith --riscv --iterations 1000
```

This needs, in your PATH:

- `llc`, `clang`, and `ld.lld` from an LLVM build with the RISC-V target
  enabled. LLVM must be from October 2026 or later, which is when the machine
  passes vsmith runs got their current names.
- Either `qemu-riscv64` (Linux), or `limactl` with a running Lima VM named `rv64`
  (macOS). When `qemu-riscv64` is not in PATH, vsmith runs each executable in
  the VM with `limactl shell rv64`.

Pass `--no-mir-exec` to skip compiling and running, and only compare interpreter
results. Other useful options are `--seed` to reproduce a run, `--workers` to
limit parallelism, and `--keep` to keep the work directory after a successful
run. It is always kept when a mismatch is found. The executable for a failing
case is left there as `<case>.elf`, so you can rerun it with `qemu-riscv64` and
debug it as described above.
