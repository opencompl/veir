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

/-- Immediate properties holding `value` as a 64-bit immediate. -/
def mkRISCVImm (value : Int) : RISCVImmediateProperties :=
  RISCVImmediateProperties.mk (BitVec.ofInt 64 value)

/-- Create a detached register-result `dst` op with immediate `value`. -/
def createRISCVImmLocal (ctx : WfIRContext OpCode)
    (dst : Riscv) (h : Riscv.propertiesOf dst = RISCVImmediateProperties)
    (operands : Array ValuePtr) (value : Int) :
    Option (WfIRContext OpCode × OperationPtr) :=
  WfRewriter.createOp! ctx dst #[RegisterType.mk] operands #[] #[]
      (cast h.symm (mkRISCVImm value)) none

/-- Create a detached register-result `dst` op without properties. -/
def createRISCVUnitLocal (ctx : WfIRContext OpCode)
    (dst : Riscv) (h : Riscv.propertiesOf dst = Unit) (operands : Array ValuePtr) :
    Option (WfIRContext OpCode × OperationPtr) :=
  WfRewriter.createOp! ctx dst #[RegisterType.mk] operands #[] #[]
      (cast h.symm ()) none

/-- The uses of `value`, each given by its user and the operand index of the use. -/
private def directUses (ctx : IRContext OpCode) (value : ValuePtr) :
    Array (OperationPtr × Nat) := Id.run do
  let mut uses := #[]
  let mut maybeUse := value.getFirstUse! ctx
  while let some use := maybeUse do
    uses := uses.push ((use.get! ctx).owner, use.index)
    maybeUse := (use.get! ctx).nextUse
  return uses

/--
  The uses of `value`, looking through chains of `builtin.unrealized_conversion_cast`s: a selected
  RISC-V instruction reads `value` through casts to `!riscv.reg` (and a selected `llvm.trunc` is
  itself a pair of casts).
-/
private def usesThroughCasts (ctx : IRContext OpCode) (value : ValuePtr) :
    Array (OperationPtr × Nat) := Id.run do
  let mut uses := #[]
  let mut worklist := directUses ctx value
  while let some (user, index) := worklist.back? do
    worklist := worklist.pop
    if user.getOpType! ctx == .builtin .unrealized_conversion_cast then
      worklist := worklist ++ directUses ctx (user.getResult 0)
    else
      uses := uses.push (user, index)
  return uses

/-- The number of bits needed to represent `value`, as LLVM's `bit_width`. -/
private def bitWidth (value : BitVec 64) : Nat :=
  if value = 0 then 0 else value.toNat.log2 + 1

/-- What a use demands of the value it reads, relative to a number of bits `bits`. -/
inductive NBitUse where
  /-- The use only demands the lower `bits` bits. -/
  | ok
  /-- The use may demand more than the lower `bits` bits. -/
  | fail
  /-- The use only demands the lower `bits` bits if all users of the user's result only demand
    its lower `bits'` bits. -/
  | forward (bits' : Nat)
deriving Inhabited, Repr, DecidableEq

/--
  What the `index`-th operand use by `user` demands of its lower `bits` bits.
  This is the `switch` of `hasAllNBitUsers` in
  https://github.com/llvm/llvm-project/blob/be52f71da1f32312784df4e04551e2185e2feb1a/llvm/lib/Target/RISCV/RISCVOptWInstrs.cpp#L119
-/
def nBitUse (ctx : IRContext OpCode) (user : OperationPtr) (index bits : Nat) : NBitUse :=
  let atLeast (n : Nat) := if bits ≥ n then NBitUse.ok else .fail
  match user.getOpType! ctx with
  | .riscv .addiw | .riscv .addw | .riscv .divuw | .riscv .divw | .riscv .mulw | .riscv .remuw
  | .riscv .remw | .riscv .sllw | .riscv .sraiw | .riscv .sraw | .riscv .srliw | .riscv .srlw
  | .riscv .subw | .riscv .rolw | .riscv .rorw | .riscv .roriw | .riscv .clzw | .riscv .ctzw
  | .riscv .cpopw | .riscv .slliuw
  -- `sext.w` is `addiw rd, rs, 0`, `negw` is `subw rd, x0, rs`.
  | .riscv .sextw | .riscv .negw =>
    atLeast 32
  | .riscv .sextb | .riscv .packh => atLeast 8
  | .riscv .sexth | .riscv .zexth | .riscv .packw => atLeast 16
  | .riscv .pack => atLeast 32
  -- If we are shifting right by less than `bits`, and users don't demand any bits that were
  -- shifted into `[bits-1:0]`, then we can consider this as a `bits`-bit user.
  | .riscv .srli =>
    let shamt := (user.getProperties! ctx Riscv.srli).value.toNat
    if bits > shamt then .forward (bits - shamt) else .fail
  -- These overwrite higher input bits, otherwise the lower word of output depends only on the
  -- lower word of input. So check their uses read W.
  | .riscv .slli =>
    let shamt := (user.getProperties! ctx Riscv.slli).value.toNat
    if bits ≥ 64 - shamt then .ok else .forward (bits + shamt)
  | .riscv .slliw =>
    let shamt := (user.getProperties! ctx Riscv.slliw).value.toNat
    if bits ≥ 32 - shamt then .ok else .forward (bits + shamt)
  | .riscv .andi =>
    if bits ≥ bitWidth (user.getProperties! ctx Riscv.andi).value then .ok else .forward bits
  -- `zext.b` is `andi rd, rs, 255`.
  | .riscv .zextb => if bits ≥ 8 then .ok else .forward bits
  | .riscv .ori =>
    if bits ≥ bitWidth (~~~(user.getProperties! ctx Riscv.ori).value) then .ok else .forward bits
  -- Operand 1 is the shift amount, which uses log2(XLen) bits.
  | .riscv .sll | .riscv .bset | .riscv .bclr | .riscv .binv =>
    if index = 1 then atLeast 6 else .forward bits
  -- Operand 1 is the shift amount or bit index, using log2(XLen) bits.
  | .riscv .sra | .riscv .srl | .riscv .rol | .riscv .ror | .riscv .bext =>
    if index = 1 then atLeast 6 else .fail
  -- Operand 0 is implicitly zero extended. `zext.w` is `add.uw rd, rs, x0`.
  | .riscv .adduw | .riscv .sh1adduw | .riscv .sh2adduw | .riscv .sh3adduw | .riscv .zextw =>
    if index = 0 && bits ≥ 32 then .ok else .forward bits
  | .riscv .bexti =>
    if (user.getProperties! ctx Riscv.bexti).value.toNat < bits then .ok else .fail
  -- Operand 0 is the value to store.
  | .riscv .sb => if index = 0 then atLeast 8 else .fail
  | .riscv .sh => if index = 0 then atLeast 16 else .fail
  | .riscv .sw => if index = 0 then atLeast 32 else .fail
  -- For these, the lower word of the output depends only on the lower word of the input. So,
  -- we check all uses only read the lower word.
  | .riscv .add | .riscv .addi | .riscv .and | .riscv .mul | .riscv .or | .riscv .sub
  | .riscv .xor | .riscv .xori | .riscv .andn | .riscv .orn | .riscv .sh1add | .riscv .sh2add
  | .riscv .sh3add | .riscv .xnor | .riscv .bseti | .riscv .bclri | .riscv .binvi
  -- `mv` is `addi rd, rs, 0`, `not` is `xori rd, rs, -1`, `neg` is `sub rd, x0, rs`.
  | .riscv .mv | .riscv .not | .riscv .neg =>
    .forward bits
  -- `orc.b` works on bytes. Round `bits` down to the nearest byte.
  | .riscv .orcb => .forward (bits / 8 * 8)
  | .riscv .czeroeqz | .riscv .czeronez => if index = 0 then .forward bits else .fail
  | _ => .fail

/--
  The pairs `(value, bits)` whose users must in turn only demand the lower `bits` bits of
  `value`, for all uses of `value` to only demand its lower `bits` bits; or `none` if some use
  of `value` may demand more.
-/
def forwardedNBitUses (ctx : IRContext OpCode) (value : ValuePtr) (bits : Nat) :
    Option (List (ValuePtr × Nat)) :=
  (usesThroughCasts ctx value).toList.foldrM (init := []) fun (user, index) acc =>
    match nBitUse ctx user index bits with
    | .ok => some acc
    | .fail => none
    | .forward bits' => some ((user.getResult 0, bits') :: acc)

/--
  Whether all users of the values in `worklist` only demand their lower `bits` bits, where
  `visited` are the pairs that were already checked, and `fuel` bounds the number of pairs that
  are still checked.
-/
def hasAllNBitUsers.go (ctx : IRContext OpCode) (fuel : Nat)
    (visited : Std.HashSet (ValuePtr × Nat)) : List (ValuePtr × Nat) → Bool
  | [] => true
  | (value, bits) :: worklist =>
    if visited.contains (value, bits) then
      hasAllNBitUsers.go ctx fuel visited worklist
    else
      match fuel, forwardedNBitUses ctx value bits with
      | 0, _ | _, none => false
      | fuel + 1, some forwarded =>
        hasAllNBitUsers.go ctx fuel (visited.insert (value, bits)) (forwarded ++ worklist)
termination_by worklist => (fuel, worklist.length)

/--
  Whether all users of `value` only demand its lower `bits` bits. We use this to select w-bit
  variants of operations such as `addw`.
  See `hasAllNBitUsers` in
  https://github.com/llvm/llvm-project/blob/be52f71da1f32312784df4e04551e2185e2feb1a/llvm/lib/Target/RISCV/RISCVOptWInstrs.cpp#L119

  Each checked pair `(value', bits')` has `value'` either `value` or the result of an operation,
  and `bits' ≤ max bits 64`, so the default `fuel` is enough to check all of them.
-/
def hasAllNBitUsers (ctx : IRContext OpCode) (value : ValuePtr) (bits : Nat)
    (fuel : Nat := (ctx.operations.size + 1) * (max bits 64 + 1)) : Bool :=
  hasAllNBitUsers.go ctx fuel ∅ [(value, bits)]

end Veir
