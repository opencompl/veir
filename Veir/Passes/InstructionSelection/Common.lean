module

public import Veir.Pass

public section

namespace Veir

/-!
  Shared helpers for the RISC-V instruction-selection lowering patterns.
-/

/--
  Create a detached `unrealized_conversion_cast : (typeof v) -> !riscv.reg`,
  returning the updated context and the register-typed cast operation. The
  caller is responsible for inserting the returned operation.
-/
def castToRegLocal (ctx : WfIRContext OpCode) (v : ValuePtr) :
    Option (WfIRContext OpCode × OperationPtr) :=
  WfRewriter.createOp! ctx Builtin.unrealized_conversion_cast
      #[RegisterType.mk] #[v] #[] #[] () none

/--
  Create a detached `unrealized_conversion_cast` from `reg` back to `op`'s
  result type, returning the updated context and the cast operation. The target
  type is read from `op`, so this is type-agnostic (it also handles non-`i64`
  results, e.g. the `!llvm.ptr` produced by `getelementptr`). The caller is
  responsible for inserting the returned operation and replacing `op`'s result
  with its result.
-/
def replaceWithRegLocal (ctx : WfIRContext OpCode) (op : OperationPtr) (reg : ValuePtr) :
    Option (WfIRContext OpCode × OperationPtr) :=
  let type := ((op.getResult 0).get! ctx.raw).type
  WfRewriter.createOp! ctx Builtin.unrealized_conversion_cast
      #[type] #[reg] #[] #[] () none

/--
  The attributes of argument or result `i`, given the `arg_attrs` or
  `res_attrs` of a call or function, if it has them.
-/
def valueAttrs (attrs? : Option Attribute) (i : Nat) : DictionaryAttr :=
  match attrs? with
  | some (.arrayAttr attrs) =>
    match attrs.value[i]? with
    | some (.dictionaryAttr dict) => dict
    | _ => .empty
  | _ => .empty

/-- The attribute `key` of `attrs`, if it has one. -/
def DictionaryAttr.get? (attrs : DictionaryAttr) (key : String) : Option Attribute :=
  (attrs.entries.find? (·.1 == key.toUTF8)).map (·.2)

/-- Whether `attrs` has the attribute `key`. -/
def DictionaryAttr.has (attrs : DictionaryAttr) (key : String) : Bool :=
  (attrs.get? key).isSome

/--
  Bring `reg`, a value of integer or pointer type `type` cast to a register, and
  so zero-extended, into the form in which the standard calling convention
  passes it, inserting any extension at `ip`. `attrs` are the value's argument
  or result attributes.

  Integers narrower than XLEN are widened according to the sign of their type
  up to 32 bits, then sign-extended (psABI, "Integer Calling Convention").
  LLVM IR records that sign as `signext` or `zeroext`. A `zeroext` value is
  already in form, as is a narrow value with neither attribute, whose upper
  bits are then unspecified. An `i32` with neither is sign-extended anyway,
  which is what C expects of it.
-/
def extendForABI (ctx : WfIRContext OpCode) (reg : ValuePtr) (type : Attribute)
    (attrs : DictionaryAttr) (ip : InsertPoint) : Option (WfIRContext OpCode × ValuePtr) := do
  let signext := attrs.has "llvm.signext"
  match type with
  | .integerType ⟨8⟩ =>
    if !signext then return (ctx, reg)
    let (ctx, op) ← WfRewriter.createOp! ctx Riscv.sextb #[RegisterType.mk] #[reg] #[] #[] () ip
    return (ctx, op.getResult 0)
  | .integerType ⟨16⟩ =>
    if !signext then return (ctx, reg)
    let (ctx, op) ← WfRewriter.createOp! ctx Riscv.sexth #[RegisterType.mk] #[reg] #[] #[] () ip
    return (ctx, op.getResult 0)
  | .integerType ⟨32⟩ =>
    if attrs.has "llvm.zeroext" then return (ctx, reg)
    let (ctx, op) ← WfRewriter.createOp! ctx Riscv.sextw #[RegisterType.mk] #[reg] #[] #[] () ip
    return (ctx, op.getResult 0)
  | _ => return (ctx, reg)

end Veir
