# `ExArray`

`ExArray` is an extensible array of bytes, similar to the standard `ByteArray`.
The main difference is that it can be extended by an arbitrary number of
zero-initialized bytes in one call.

It is implemented in C, by always keeping the backing array zero initialized.

## Dependencies

Depends on the project's Lean toolchain, GMP development headers, and `pkg-config`
(or `pkgconf`).
Lake uses Lean's bundled compiler, archiver, and linker to build the native C code with
LTO.
Override the compiler and archiver with `LEAN_CC` and `LEAN_AR`, using tools
compatible with the linker for LTO.
Use `direnv` or `nix develop` from the repository root to supply dependencies via nix.

To test, run `lake exe test` from this directory or `make tests` from the parent
directory to run alongside VeIR's test suites.
