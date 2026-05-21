# `ExArray`

`ExArray` is an extensible array of bytes, similar to the standard `ByteArray`.
The main difference is that it can be extended by an arbitrary number of
zero-initialized bytes in one call.

It is implemented in C, by always keeping the backing array zero initialized.
