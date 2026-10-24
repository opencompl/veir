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

Without an explicit emit mode, `vcc` produces a 64-bit RISC-V Linux
executable using VeIR's own RISC-V backend. VeIR selects instructions, and
`llc` allocates registers and prints the assembly, which `clang` then assembles
and links. Pass `--llvm-backend` to instead translate VeIR's output back to
LLVM IR and let `clang` generate the code. This is useful for programs that use
constructs VeIR's backend can't handle yet, such as `switch` statements and
some stack allocations. Either way, this needs the environment described in
[Setting up a RISC-V user-mode environment](#setting-up-a-risc-v-user-mode-environment).
For example, [`Test/Vcc/primes.c`](Test/Vcc/primes.c) returns the 10th prime
number, 29, as its exit status:
```bash
Tools/vcc Test/Vcc/primes.c -o primes
./primes; echo $?
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
  qemu-user qemu-user-binfmt gdb-multiarch
```

`qemu-user-binfmt` registers QEMU with the kernel so that riscv64 executables
can be run directly. Dynamically linked executables also need to find the
riscv64 C library:
```bash
export QEMU_LD_PREFIX=/usr/riscv64-linux-gnu
```

`Tools/vcc` and `Tools/vsmith` also need LLVM 24 or later, since VeIR's backend
relies on machine pass names that LLVM 23 doesn't have. Until LLVM 24 is
released, the distributions don't package it, but [apt.llvm.org](https://apt.llvm.org)
has nightly snapshots. Its `llvm.sh` script adds the repository and installs
clang and lld; `llc`, `opt`, and the MLIR tools are separate packages:
```bash
wget https://apt.llvm.org/llvm.sh
sudo bash llvm.sh 24
sudo apt-get install -y llvm-24 mlir-24-tools
export PATH=/usr/lib/llvm-24/bin:$PATH
```

Alternatively, put the `bin` directory of your own LLVM build first in `PATH`.

### macOS

`qemu-riscv64` only runs on Linux hosts, so on macOS the emulator runs inside a
small Linux VM managed by [Lima](https://lima-vm.io). Create a VM named `rv64`
(this is the name `vsmith` looks for). Your home directory is mounted in the VM
at the same path:
```bash
brew install lima
limactl start --name=rv64 --vm-type=vz --mount-writable template:ubuntu-24.04
```

Then install the packages from the Linux section inside the VM. Set
`QEMU_LD_PREFIX` in the VM's `/etc/environment` rather than a shell profile, so
that commands run with `limactl shell rv64 <command>` see it too. Lima reuses its
SSH connection, so `--reconnect` is needed once for the setting to take effect:
```bash
limactl shell rv64 sudo apt-get update
limactl shell rv64 sudo apt-get install -y \
  gcc-riscv64-linux-gnu g++-riscv64-linux-gnu libc6-dev-riscv64-cross \
  qemu-user qemu-user-binfmt gdb-multiarch clang lld
limactl shell rv64 sh -c \
  "echo QEMU_LD_PREFIX=/usr/riscv64-linux-gnu | sudo tee -a /etc/environment"
limactl shell --reconnect rv64 true
```

Use `limactl shell rv64` to open a shell in the VM, or `limactl shell rv64
<command>` to run a single command. `limactl stop rv64` and `limactl start
rv64` stop and restart it. Inside the VM, your macOS home directory is at the
same path (for example `/Users/<you>`), but the VM's own `~` is a different
directory.

To compile for riscv64 Linux on the Mac itself, as `Tools/vcc` does, you need
LLVM 24 or later in `PATH` (until it is released, build LLVM from source with
the `mlir` and `lld` projects enabled). clang also needs a copy of the VM's
riscv64 headers and libraries. Copy them out of the VM
and point `RISCV_SYSROOT` at the copy (add the `export` to your shell profile):
```bash
mkdir -p ~/.local/riscv64-linux-gnu-sysroot
limactl shell rv64 tar -C / -cf - usr/riscv64-linux-gnu usr/lib/gcc-cross/riscv64-linux-gnu \
  | tar -C ~/.local/riscv64-linux-gnu-sysroot -xf -
export RISCV_SYSROOT=~/.local/riscv64-linux-gnu-sysroot
```

Then link with `lld`, and run the result in the VM:
```bash
clang --target=riscv64-linux-gnu --sysroot=$RISCV_SYSROOT -fuse-ld=lld -O2 Test/Vcc/primes.c -o primes-rv
limactl shell rv64 $PWD/primes-rv
```

The program must be under your home directory for the VM to see it.

### Checking the setup

On Linux, or in a shell inside the VM on macOS, from the root of this repository
(each program should exit with status 29):
```bash
riscv64-linux-gnu-gcc -O2 Test/Vcc/primes.c -o primes-rv; ./primes-rv; echo $?
riscv64-linux-gnu-gcc -O2 -static Test/Vcc/primes.c -o primes-rv-static; ./primes-rv-static; echo $?
clang --target=riscv64-linux-gnu -O2 Test/Vcc/primes.c -o primes-clang; ./primes-clang; echo $?
```

To debug a program, start it under QEMU's GDB stub and attach `gdb-multiarch`:
```bash
qemu-riscv64 -g 1234 ./primes-rv-static &
gdb-multiarch -ex 'set architecture riscv:rv64' -ex 'target remote :1234' ./primes-rv-static
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

- `llc`, `clang`, and `ld.lld` from LLVM 24 or later, with the RISC-V target
  enabled (see [Linux](#linux)).
- Either `qemu-riscv64` (Linux), or `limactl` with a running Lima VM named `rv64`
  (macOS). When `qemu-riscv64` is not in PATH, vsmith runs each executable in
  the VM with `limactl shell rv64`.

Pass `--no-mir-exec` to skip compiling and running, and only compare interpreter
results. Other useful options are `--seed` to reproduce a run, `--workers` to
limit parallelism, and `--keep` to keep the work directory after a successful
run. It is always kept when a mismatch is found. The executable for a failing
case is left there as `<case>.elf`, so you can rerun it with `qemu-riscv64` and
debug it as described above.
