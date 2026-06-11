# `ExArray`

`ExArray` is an extensible array of bytes, similar to the standard `ByteArray`.
The main difference is that it can be extended by an arbitrary number of
zero-initialized bytes in one call.

It is implemented in C, by always keeping the backing array zero initialized.

## Dependencies

One needs to have `gmp`, `pkgconf` and `llvm` installed (on MacOS, `llvm` should
be installed with brew as the Apple-shipped version does not ship with
`llvm-ar`), and to source `.envrc` in the parent directory, which can be
automated with `direnv`.
