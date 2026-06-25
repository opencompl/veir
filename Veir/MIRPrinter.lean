module

public import Veir.IR.Basic
public import Veir.Properties
public import Veir.GlobalOpInfo

import Veir.IR.Grind

open Veir

public section

/-!
  # VeIR RISC-V dialect → LLVM pre-register-allocation MIR

  A small, intentionally non-general printer: it takes a `main : i64 ()`
  function whose body has already been lowered to the `riscv` / `riscv_cf`
  dialects (the output of the `isel-*` pipeline) and emits textual MIR with
  virtual registers, suitable for `llc -run-pass=none` / `-start-before=...`.

  Two structural translations happen here:
  * VeIR block arguments become MIR `PHI`s at join blocks (or a `COPY` when a
    block has a single predecessor).
  * `builtin.unrealized_conversion_cast` (reg ↔ i64/i1) becomes a `COPY`.
-/

namespace Veir.MIRPrinter

/-- Virtual-register name for a value: `%v<opId>` for op results,
    `%arg<blockId>_<i>` for block arguments. -/
def vreg (ctx : IRContext OpCode) (v : ValuePtr) : String :=
  match v with
  | .opResult rp => s!"%v{(rp.get! ctx).owner.id}"
  | .blockArgument bp =>
    let a := bp.get! ctx
    s!"%arg{a.owner.id}_{a.index}"

/-- The integer `value` property of an op (immediate operations), if present. -/
def immValue? (ctx : IRContext OpCode) (op : OperationPtr) : Option Int :=
  let opType := op.getOpType! ctx
  let d := Properties.toAttrDict opType (op.getProperties! ctx opType)
  match d["value".toUTF8]? with
  | some (.integerAttr a) => some a.value
  | _ => none

/-- The `operandSegmentSizes` property of a branch op, if present. -/
def segments? (ctx : IRContext OpCode) (op : OperationPtr) : Option (Array Int) :=
  let opType := op.getOpType! ctx
  let d := Properties.toAttrDict opType (op.getProperties! ctx opType)
  match d["operandSegmentSizes".toUTF8]? with
  | some (.denseArrayAttr a) => some a.values
  | _ => none

/-- All operands of `op` as an array. -/
def getOperands (ctx : IRContext OpCode) (op : OperationPtr) : Array ValuePtr := Id.run do
  let mut a := #[]
  for i in 0...(op.getNumOperands! ctx) do
    a := a.push (op.getOperand! ctx i)
  return a

/-- The terminator (last op) of a block, given its first op. -/
partial def lastOp (ctx : IRContext OpCode) (op : OperationPtr) : OperationPtr :=
  match (op.get! ctx).next with
  | some n => lastOp ctx n
  | none => op

/-- Blocks of a region, in order. -/
partial def collectBlocks (ctx : IRContext OpCode) (b : Option BlockPtr)
    (acc : Array BlockPtr := #[]) : Array BlockPtr :=
  match b with
  | none => acc
  | some bp => collectBlocks ctx (bp.get! ctx).next (acc.push bp)

/-- Index of the block with the given id within `blocks`. -/
def bbOf (blocks : Array BlockPtr) (id : Nat) : Nat := Id.run do
  for i in 0...blocks.size do
    if (blocks[i]!).id == id then return i
  return 0

/-- Successor block ids of a block (via its terminator). -/
def succIds (ctx : IRContext OpCode) (b : BlockPtr) : List Nat :=
  match (b.get! ctx).firstOp with
  | none => []
  | some f =>
    let term := lastOp ctx f
    (List.range (term.getNumSuccessors! ctx)).map (fun k => (term.getSuccessor! ctx k).id)

/-- Block ids reachable from the entry, via a worklist over successors. -/
partial def reachable (ctx : IRContext OpCode) (blocks : Array BlockPtr)
    (work : List Nat) (seen : List Nat := []) : List Nat :=
  match work with
  | [] => seen
  | id :: rest =>
    if seen.contains id then reachable ctx blocks rest seen
    else reachable ctx blocks (succIds ctx (blocks[bbOf blocks id]!) ++ rest) (id :: seen)

/-- Reg-reg mnemonic for a riscv opcode. -/
def regRegMnem : Riscv → Option String
  | .add => "ADD"   | .sub => "SUB"   | .sll => "SLL"   | .srl => "SRL"
  | .sra => "SRA"   | .slt => "SLT"   | .sltu => "SLTU" | .xor => "XOR"
  | .or => "OR"     | .and => "AND"   | .mul => "MUL"   | .mulh => "MULH"
  | .mulhu => "MULHU" | .mulhsu => "MULHSU" | .div => "DIV" | .divu => "DIVU"
  | .rem => "REM"   | .remu => "REMU"
  | .addw => "ADDW" | .subw => "SUBW" | .sllw => "SLLW" | .srlw => "SRLW"
  | .sraw => "SRAW" | .mulw => "MULW" | .divw => "DIVW" | .divuw => "DIVUW"
  | .remw => "REMW" | .remuw => "REMUW"
  -- Zbb / Zbs / Zba / Zicond
  | .andn => "ANDN" | .orn => "ORN"   | .xnor => "XNOR"
  | .min => "MIN"   | .max => "MAX"   | .minu => "MINU" | .maxu => "MAXU"
  | .rol => "ROL"   | .ror => "ROR"   | .rolw => "ROLW" | .rorw => "RORW"
  | .czeroeqz => "CZERO_EQZ" | .czeronez => "CZERO_NEZ"
  | .bclr => "BCLR" | .bext => "BEXT" | .binv => "BINV" | .bset => "BSET"
  | .pack => "PACK" | .packh => "PACKH" | .packw => "PACKW"
  | .sh1add => "SH1ADD" | .sh2add => "SH2ADD" | .sh3add => "SH3ADD"
  | .adduw => "ADD_UW"
  | .sh1adduw => "SH1ADD_UW" | .sh2adduw => "SH2ADD_UW" | .sh3adduw => "SH3ADD_UW"
  | _ => none

/-- Reg-imm mnemonic for a riscv opcode (immediate in the `value` property). -/
def regImmMnem : Riscv → Option String
  | .addi => "ADDI" | .slti => "SLTI" | .sltiu => "SLTIU" | .andi => "ANDI"
  | .ori => "ORI"   | .xori => "XORI" | .slli => "SLLI"  | .srli => "SRLI"
  | .srai => "SRAI" | .addiw => "ADDIW" | .slliw => "SLLIW" | .srliw => "SRLIW"
  | .sraiw => "SRAIW"
  | .rori => "RORI" | .roriw => "RORIW" | .slliuw => "SLLI_UW"
  | .bclri => "BCLRI" | .bexti => "BEXTI" | .binvi => "BINVI" | .bseti => "BSETI"
  | _ => none

/-- Unary (single reg operand, no immediate) mnemonic for a riscv opcode. -/
def unaryMnem : Riscv → Option String
  | .clz => "CLZ"   | .ctz => "CTZ"   | .cpop => "CPOP"
  | .clzw => "CLZW" | .ctzw => "CTZW" | .cpopw => "CPOPW"
  | .orcb => "ORC_B" | .rev8 => "REV8_RV64"
  | .sextb => "SEXT_B" | .sexth => "SEXT_H" | .zexth => "ZEXT_H_RV64"
  | _ => none

/-- The block-argument values passed to each successor of a terminator. -/
def succArgs (ctx : IRContext OpCode) (term : OperationPtr) : Array (Array ValuePtr) := Id.run do
  let nsucc := term.getNumSuccessors! ctx
  let ops := getOperands ctx term
  let segs := segments? ctx term
  -- first segment (if any) is the comparison operands, not block args
  let mut off := match segs with | some s => (s[0]!).toNat | none => 0
  let mut res := #[]
  for k in 0...nsucc do
    let nk := match segs with | some s => (s[k+1]!).toNat | none => ops.size
    res := res.push (ops.extract off (off + nk))
    off := off + nk
  return res

/-- A degenerate conditional branch (both successors the same block) that passes
    *different* arguments on its two edges is a value selection we can't lower by
    collapsing to one edge; it needs edge-splitting, which we don't do yet. -/
def hasUnsupportedDegenerate (ctx : IRContext OpCode) (blocks : Array BlockPtr) : Bool := Id.run do
  for bi in 0...blocks.size do
    match (blocks[bi]!).get! ctx |>.firstOp with
    | none => pure ()
    | some f =>
      let term := lastOp ctx f
      if term.getNumSuccessors! ctx == 2 &&
         (term.getSuccessor! ctx 0).id == (term.getSuccessor! ctx 1).id then
        let a := succArgs ctx term
        if (a[0]!).map (vreg ctx) != (a[1]!).map (vreg ctx) then
          return true
  return false

/-- For each block (by index), its predecessors as (predBlockIndex, argValues). -/
def computePreds (ctx : IRContext OpCode) (blocks : Array BlockPtr) :
    Array (Array (Nat × Array ValuePtr)) := Id.run do
  let mut preds := #[]
  for _ in 0...blocks.size do
    preds := preds.push #[]
  for bi in 0...blocks.size do
    match (blocks[bi]!).get! ctx |>.firstOp with
    | none => pure ()
    | some f =>
      let term := lastOp ctx f
      let args := succArgs ctx term
      -- A conditional branch whose successors are the same block becomes a
      -- single edge: record each target block at most once per terminator.
      -- (Only reached when those edges carry identical args; see
      -- hasUnsupportedDegenerate.)
      let mut seenTargets : List Nat := []
      for k in 0...term.getNumSuccessors! ctx do
        let tid := (term.getSuccessor! ctx k).id
        if !seenTargets.contains tid then
          seenTargets := tid :: seenTargets
          let ti := bbOf blocks tid
          preds := preds.set! ti (preds[ti]!.push (bi, args[k]!))
  return preds

/-- Emit a single non-terminator operation. -/
def emitRegular (ctx : IRContext OpCode) (op : OperationPtr) : IO Unit := do
  let opType := op.getOpType! ctx
  let ops := getOperands ctx op
  let res := s!"%v{op.id}:gpr"
  let v := fun (i : Nat) => vreg ctx (ops[i]!)
  let imm := (immValue? ctx op).getD 0
  match opType with
  | .builtin .unrealized_conversion_cast =>
    IO.println s!"    {res} = COPY {v 0}"
  | .riscv rop =>
    match rop with
    | .li => IO.println s!"    {res} = PseudoLI {imm}"
    -- pseudo-instructions that expand to a specific real instruction form
    | .mv => IO.println s!"    {res} = COPY {v 0}"
    | .not => IO.println s!"    {res} = XORI {v 0}, -1"
    | .neg => IO.println s!"    {res} = SUB $x0, {v 0}"
    | .negw => IO.println s!"    {res} = SUBW $x0, {v 0}"
    | .seqz => IO.println s!"    {res} = SLTIU {v 0}, 1"
    | .snez => IO.println s!"    {res} = SLTU $x0, {v 0}"
    | .sltz => IO.println s!"    {res} = SLT {v 0}, $x0"
    | .sgtz => IO.println s!"    {res} = SLT $x0, {v 0}"
    | .sextw => IO.println s!"    {res} = ADDIW {v 0}, 0"
    | .zextw => IO.println s!"    {res} = ADD_UW {v 0}, $x0"
    | .zextb => IO.println s!"    {res} = ANDI {v 0}, 255"
    | _ =>
      match unaryMnem rop with
      | some m => IO.println s!"    {res} = {m} {v 0}"
      | none =>
        match regImmMnem rop with
        | some m => IO.println s!"    {res} = {m} {v 0}, {imm}"
        | none =>
          match regRegMnem rop with
          | some m => IO.println s!"    {res} = {m} {v 0}, {v 1}"
          | none => IO.println s!"    ; UNHANDLED {reprStr rop}"
  | _ => IO.println s!"    ; UNHANDLED op"

/-- Emit a terminator operation (branch / return). -/
def emitTerminator (ctx : IRContext OpCode) (blocks : Array BlockPtr)
    (op : OperationPtr) : IO Unit := do
  let opType := op.getOpType! ctx
  let ops := getOperands ctx op
  let v := fun (i : Nat) => vreg ctx (ops[i]!)
  let succ := fun (k : Nat) => bbOf blocks (op.getSuccessor! ctx k).id
  -- Degenerate conditional branch (both targets identical) → unconditional jump.
  if op.getNumSuccessors! ctx == 2 && succ 0 == succ 1 then
    IO.println s!"    PseudoBR %bb.{succ 0}"
    return
  match opType with
  | .riscv_cf .branch =>
    IO.println s!"    PseudoBR %bb.{succ 0}"
  | .riscv_cf .bnez =>
    IO.println s!"    BNE {v 0}, $x0, %bb.{succ 0}"
    IO.println s!"    PseudoBR %bb.{succ 1}"
  | .riscv_cf .beqz =>
    IO.println s!"    BEQ {v 0}, $x0, %bb.{succ 0}"
    IO.println s!"    PseudoBR %bb.{succ 1}"
  | .riscv_cf .beq =>
    IO.println s!"    BEQ {v 0}, {v 1}, %bb.{succ 0}"
    IO.println s!"    PseudoBR %bb.{succ 1}"
  | .riscv_cf .bne =>
    IO.println s!"    BNE {v 0}, {v 1}, %bb.{succ 0}"
    IO.println s!"    PseudoBR %bb.{succ 1}"
  | .riscv_cf .blt =>
    IO.println s!"    BLT {v 0}, {v 1}, %bb.{succ 0}"
    IO.println s!"    PseudoBR %bb.{succ 1}"
  | .riscv_cf .bge =>
    IO.println s!"    BGE {v 0}, {v 1}, %bb.{succ 0}"
    IO.println s!"    PseudoBR %bb.{succ 1}"
  | .riscv_cf .bltu =>
    IO.println s!"    BLTU {v 0}, {v 1}, %bb.{succ 0}"
    IO.println s!"    PseudoBR %bb.{succ 1}"
  | .riscv_cf .bgeu =>
    IO.println s!"    BGEU {v 0}, {v 1}, %bb.{succ 0}"
    IO.println s!"    PseudoBR %bb.{succ 1}"
  | .llvm .return | .func .return =>
    if ops.size > 0 then
      IO.println s!"    $x10 = COPY {v 0}"
      IO.println s!"    PseudoRET implicit $x10"
    else
      IO.println s!"    PseudoRET"
  | _ => IO.println s!"    ; UNHANDLED terminator"

/-- Emit the op list of a block, treating the last op as the terminator. -/
partial def emitOps (ctx : IRContext OpCode) (blocks : Array BlockPtr)
    (op : OperationPtr) : IO Unit := do
  match (op.get! ctx).next with
  | some n =>
    emitRegular ctx op
    emitOps ctx blocks n
  | none =>
    emitTerminator ctx blocks op

/-- Emit one basic block: label, successors, PHIs, then instructions. -/
def emitBlock (ctx : IRContext OpCode) (blocks : Array BlockPtr)
    (preds : Array (Array (Nat × Array ValuePtr))) (bi : Nat) : IO Unit := do
  let b := blocks[bi]!
  IO.println s!"  bb.{bi}:"
  -- successors line, from the terminator
  match (b.get! ctx).firstOp with
  | some f =>
    let term := lastOp ctx f
    let nsucc := term.getNumSuccessors! ctx
    if nsucc != 0 then
      -- distinct successor block indices, in order
      let mut sis : List Nat := []
      for k in 0...nsucc do
        let si := bbOf blocks (term.getSuccessor! ctx k).id
        if !sis.contains si then sis := sis ++ [si]
      let parts := sis.map (fun si => s!"%bb.{si}")
      IO.println s!"    successors: {String.intercalate ", " parts}"
  | none => pure ()
  -- block arguments → PHI (or COPY for a single predecessor)
  let np := b.getNumArguments! ctx
  if np != 0 then
    let plist := preds[bi]!
    for ai in 0...np do
      let name := s!"%arg{b.id}_{ai}"
      if plist.size == 0 then
        IO.println s!"    {name}:gpr = IMPLICIT_DEF"
      else if plist.size == 1 then
        let (_, vals) := plist[0]!
        IO.println s!"    {name}:gpr = COPY {vreg ctx (vals[ai]!)}"
      else
        let parts := plist.toList.map (fun (pbi, vals) => s!"{vreg ctx (vals[ai]!)}, %bb.{pbi}")
        IO.println s!"    {name}:gpr = PHI {String.intercalate ", " parts}"
  -- instructions
  match (b.get! ctx).firstOp with
  | some f => emitOps ctx blocks f
  | none => pure ()

/-- Print a full MIR module for the given `main` function. -/
def printMIR (ctx : IRContext OpCode) (funcOp : OperationPtr) : IO Unit := do
  let region := funcOp.getRegion! ctx 0
  let allBlocks := collectBlocks ctx (region.get! ctx).firstBlock
  -- Drop blocks unreachable from the entry: a real codegen prunes them, and
  -- they break MIR liveness (their values aren't dominated by any real path).
  let reach :=
    if allBlocks.isEmpty then []
    else reachable ctx allBlocks [(allBlocks[0]!).id]
  let blocks := allBlocks.filter (fun b => reach.contains b.id)
  if hasUnsupportedDegenerate ctx blocks then
    IO.println "; UNHANDLED: degenerate same-target conditional branch with differing block arguments (needs edge split)"
    return
  let preds := computePreds ctx blocks
  IO.println "--- |"
  IO.println "  define i64 @main() #0 {"
  IO.println "    ret i64 0"
  IO.println "  }"
  IO.println "  attributes #0 = { \"target-features\"=\"+m,+zba,+zbb,+zbs,+zbc,+zbkb,+zicond\" }"
  IO.println "..."
  IO.println "---"
  IO.println "name:            main"
  IO.println "tracksRegLiveness: true"
  IO.println "body:             |"
  for bi in 0...blocks.size do
    if bi != 0 then IO.println ""
    emitBlock ctx blocks preds bi
  IO.println "..."

end Veir.MIRPrinter
