import Lake
open System Lake DSL

package exarray where
  srcDir := "lean"

/-! ## Static C FFI Library -/

input_file ffi_static.c where
  path := "c" / "ffi_static.c"
  text := true

target ffi_static.o pkg : FilePath := do
  let srcJob ← ffi_static.c.fetch
  let oFile := pkg.buildDir / "c" / "ffi_static.o"
  let gmpInclude ← captureProc {cmd := "pkg-config", args := #["--variable=includedir", "gmp"]}
  let multiarch ← captureProc {cmd := "cc", args := #["-print-multiarch"]}
  -- Use Lean's compiler and headers, matching buildStaticLib and executable linking.
  buildLeanO oFile srcJob #["-I", gmpInclude, "-I", "/usr/include/" ++ multiarch]
    #["-std=c11", "-fPIC", "-flto=full", "-O3", "-DLEAN_USE_GMP", "-fwrapv"]

target libleanffi_static pkg : FilePath := do
  let ffiO ← ffi_static.o.fetch
  let name := nameToStaticLib "leanffi"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

@[default_target]
lean_lib ExArray where
  moreLinkObjs := #[libleanffi_static]

lean_exe test where
  root := `Main
  moreLinkArgs := #["-flto=full"]
  moreLeancArgs := #["-flto=full"]
