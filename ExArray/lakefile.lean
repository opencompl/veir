import Lake
open System Lake DSL

package exarray where
  srcDir := "lean"

/-! ## Static C FFI Library -/

input_file ffi_static.c where
  path := "c" / "ffi_static.cpp"
  text := true

target ffi_static.o pkg : FilePath := do
  let srcJob ← ffi_static.c.fetch
  let oFile := pkg.buildDir / "c" / "ffi_static.o"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-std=c++23", "-fPIC", "-flto=full"] (pkg.dir / "compiler") getLeanTrace

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
