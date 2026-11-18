import Veir.IR.RootedIso
import Veir.Input
import Veir.Rewriter.WfRewriter

open Veir

namespace RootedIsoTest

/-- Padding changes allocation IDs without changing the function under comparison. -/
def parseFunction (body : String) (padding : Bool := false) (verify : Bool := true) :
    Except String (WfIRContext OpCode × OperationPtr) := do
  let dummy := if padding then
    r#""llvm.func"() <{sym_name = "padding", function_type = !llvm.func<void ()>}> ({
      "llvm.return"() : () -> ()
    }) : () -> ()"# else ""
  let source := "\"builtin.module\"() ({\n" ++ dummy ++ body ++ "\n}) : () -> ()"
  let (ctx, root, _) ← Input.parseSourceString source.toUTF8 (verifyAfterParse := verify)
  let some block := (root.getRegion! ctx.raw 0).getFirstBlock! ctx.raw
    | throw "missing module block"
  let some function := block.getLastOp! ctx.raw | throw "missing function"
  return (ctx, function)

def diamond : String := r#"
  "llvm.func"() <{sym_name = "f", function_type = !llvm.func<i32 (i1, i32, i32)>}> ({
  ^entry(%c : i1, %x : i32, %y : i32):
    "llvm.cond_br"(%c, %x, %y) [^left, ^right]
      <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
  ^left(%l : i32):
    "llvm.br"(%l) [^join] : (i32) -> ()
  ^right(%r : i32):
    "llvm.br"(%r) [^join] : (i32) -> ()
  ^join(%v : i32):
    "llvm.return"(%v) : (i32) -> ()
  }) : () -> ()
"#

def forwardReference : String := r#"
  "llvm.func"() <{sym_name = "f", function_type = !llvm.func<i32 ()>}> ({
    %early = "llvm.xor"(%late, %late) : (i32, i32) -> i32
    %late = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    "llvm.return"(%early) : (i32) -> ()
  }) : () -> ()
"#

def sharing : String := r#"
  "llvm.func"() <{sym_name = "f", function_type = !llvm.func<i32 ()>}> ({
    %a = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %b = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %result = "llvm.xor"(%a, %a) : (i32, i32) -> i32
    "llvm.return"(%result) : (i32) -> ()
  }) : () -> ()
"#

def check (label : String) (a b : WfIRContext OpCode × OperationPtr) (expected : Bool) : IO Unit := do
  unless rootedIso? a.1 a.2 b.1 b.2 == expected do
    throw (IO.userError s!"{label}: unexpected rooted isomorphism result")

-- In particular, changing only a successor must fail even when sibling blocks look identical.
#eval show IO Unit from do
  let a ← IO.ofExcept (parseFunction diamond)
  let b ← IO.ofExcept (parseFunction diamond true)
  unless a.2 != b.2 do throw (IO.userError "fixture did not change allocation IDs")
  check "reflexivity" a a true
  check "renaming and unreachable allocations" a b true
  check "reverse renaming" b a true
  let swapped ← IO.ofExcept (parseFunction (diamond.replace "[^left, ^right]" "[^right, ^left]"))
  check "successor order" a swapped false
  let arguments ← IO.ofExcept (parseFunction (diamond.replace "(%c, %x, %y)" "(%c, %y, %x)"))
  check "forwarded arguments" a arguments false
  let loop := diamond.replace "\"llvm.br\"(%r) [^join]" "\"llvm.br\"(%r) [^right]"
  let loop₁ ← IO.ofExcept (parseFunction loop)
  let loop₂ ← IO.ofExcept (parseFunction loop true)
  check "loop backedge" loop₁ loop₂ true
  check "changed loop backedge" a loop₁ false
  let forward₁ ← IO.ofExcept (parseFunction forwardReference (verify := false))
  let forward₂ ← IO.ofExcept (parseFunction forwardReference true false)
  check "forward SSA reference" forward₁ forward₂ true
  let changed ← IO.ofExcept (parseFunction (forwardReference.replace "7 : i32" "8 : i32") true false)
  check "constant properties" forward₁ changed false
  let shared ← IO.ofExcept (parseFunction sharing)
  let unshared ← IO.ofExcept (parseFunction (sharing.replace "(%a, %a)" "(%a, %b)"))
  check "inconsistent SSA renaming" shared unshared false

def literalFunction : String := r#"
  "llvm.func"() <{sym_name = "f", function_type = !llvm.func<i32 ()>}> ({
    %inside = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    "llvm.return"(%inside) : (i32) -> ()
  }) : () -> ()
"#

/-- Keep the local constant, but return a separately allocated, detached constant. -/
def externalReference (value : Int) : Except String (WfIRContext OpCode × OperationPtr) := do
  let (ctx, root) ← parseFunction literalFunction
  let some block := (root.getRegion! ctx.raw 0).getFirstBlock! ctx.raw | throw "missing body"
  let some ret := block.getLastOp! ctx.raw | throw "missing return"
  let some (ctx, outside) := WfRewriter.createOp! ctx Llvm.mlir__constant
      #[TypeAttr.of IntegerType (.signless 32)] #[] #[] #[]
      (LLVMConstantProperties.mk (.integer (IntegerAttr.ofInt value (.signless 32)))) none
    | throw "could not allocate external constant"
  return (WfRewriter.replaceOperand! ctx (ret.getOpOperand 0) (.opResult (outside.getResult 0)), root)

#eval show IO Unit from do
  let contained ← IO.ofExcept (parseFunction literalFunction)
  let external₇ ← IO.ofExcept (externalReference 7)
  let external₉₉ ← IO.ofExcept (externalReference 99)
  let external₁₀₀ ← IO.ofExcept (externalReference 100)
  check "external definition cannot alias a contained definition" external₇ contained false
  check "reverse external alias" contained external₇ false
  check "external definitions are compared" external₉₉ external₁₀₀ false
  check "matching external definitions" external₉₉ (← IO.ofExcept (externalReference 99)) true
  let invalid : WfIRContext OpCode × OperationPtr := (contained.1, { id := 1000000 })
  check "out-of-bounds roots" invalid invalid false

end RootedIsoTest
