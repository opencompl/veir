module

public import Veir.IR.Basic
public import Veir.Properties
public import Veir.GlobalOpInfo
public import Veir.Interfaces.FunctionInterfaces

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

/-- The physical-register MIR name (e.g. `$x0`) named by a register type
    carrying an index, if any. -/
def physRegName? : Attribute → Option String
  | .registerType { index := some n } => some s!"$x{n}"
  | _ => none

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

/-- The lowered CFG: predecessors of every block (real + synthetic), which real
    blocks have a split branch, and the trampoline blocks to emit.

    A degenerate conditional branch (both successors the same block S) that passes
    *different* arguments on its two edges is a value selection.  MIR forbids a
    block listing S twice or a PHI taking two values from the same predecessor, so
    we split the edge: route the two sides through fresh single-jump trampoline
    blocks t0/t1, each forwarding to S, so S's PHI gets one entry per trampoline.
    Equal-argument degenerate branches need no split (collapsed to one edge). -/
structure EdgePlan where
  /-- preds[i] = predecessors of block i as (predBlockIndex, argValues). -/
  preds : Array (Array (Nat × Array ValuePtr))
  /-- split[bi] = some (t0, t1) if real block bi's branch is edge-split. -/
  split : Array (Option (Nat × Nat))
  /-- trampolines to emit, as (trampolineIndex, targetBlockIndex), in index order. -/
  tramps : Array (Nat × Nat)

def planEdges (ctx : IRContext OpCode) (blocks : Array BlockPtr) : EdgePlan := Id.run do
  let n := blocks.size
  -- Pass 1: assign trampoline indices to degenerate branches with differing args.
  let mut split : Array (Option (Nat × Nat)) := #[]
  for _ in 0...n do
    split := split.push none
  let mut tramps : Array (Nat × Nat) := #[]
  let mut trampEdges : Array (Nat × Nat × Array ValuePtr) := #[]
  let mut nextIdx := n
  for bi in 0...n do
    match (blocks[bi]!).get! ctx |>.firstOp with
    | none => pure ()
    | some f =>
      let term := lastOp ctx f
      if term.getNumSuccessors! ctx == 2 &&
         (term.getSuccessor! ctx 0).id == (term.getSuccessor! ctx 1).id then
        let a := succArgs ctx term
        if (a[0]!).map (vreg ctx) != (a[1]!).map (vreg ctx) then
          let s := bbOf blocks (term.getSuccessor! ctx 0).id
          let t0 := nextIdx
          let t1 := nextIdx + 1
          nextIdx := nextIdx + 2
          split := split.set! bi (some (t0, t1))
          tramps := (tramps.push (t0, s)).push (t1, s)
          trampEdges := (trampEdges.push (t0, s, a[0]!)).push (t1, s, a[1]!)
  let total := nextIdx
  -- Pass 2: predecessors for every block (real blocks + trampolines).
  let mut preds : Array (Array (Nat × Array ValuePtr)) := #[]
  for _ in 0...total do
    preds := preds.push #[]
  for bi in 0...n do
    match (blocks[bi]!).get! ctx |>.firstOp with
    | none => pure ()
    | some f =>
      match split[bi]! with
      | some _ => pure ()  -- this block's edges flow through its trampolines
      | none =>
        let term := lastOp ctx f
        let args := succArgs ctx term
        -- record each distinct target at most once (collapses equal-arg degenerates)
        let mut seenTargets : List Nat := []
        for k in 0...term.getNumSuccessors! ctx do
          let tid := (term.getSuccessor! ctx k).id
          if !seenTargets.contains tid then
            seenTargets := tid :: seenTargets
            let ti := bbOf blocks tid
            preds := preds.set! ti (preds[ti]!.push (bi, args[k]!))
  for e in trampEdges do
    preds := preds.set! e.2.1 (preds[e.2.1]!.push (e.1, e.2.2))
  return { preds := preds, split := split, tramps := tramps }

/-- Emit a single non-terminator operation. -/
def emitRegular (ctx : IRContext OpCode) (op : OperationPtr) : IO Unit := do
  let opType := op.getOpType! ctx
  let ops := getOperands ctx op
  let res := s!"%v{op.id}:gpr"
  let v := fun (i : Nat) => vreg ctx (ops[i]!)
  let imm := (immValue? ctx op).getD 0
  match opType with
  | .builtin .unrealized_conversion_cast =>
    let operandAttr := (op.getOperandTypes! ctx)[0]?.map (·.val)
    match operandAttr with
    | some (Attribute.integerType { bitwidth := 32 , .. }) =>
      IO.println s!"    {res} = PseudoZEXT_W {v 0}"
    | _ => IO.println s!"    {res} = COPY {v 0}"
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
    -- memory: loads (result ← mem[base + imm])
    | .ld  => IO.println s!"    {res} = LD {v 0}, {imm}"
    | .lw  => IO.println s!"    {res} = LW {v 0}, {imm}"
    | .lwu => IO.println s!"    {res} = LWU {v 0}, {imm}"
    | .lh  => IO.println s!"    {res} = LH {v 0}, {imm}"
    | .lhu => IO.println s!"    {res} = LHU {v 0}, {imm}"
    | .lb  => IO.println s!"    {res} = LB {v 0}, {imm}"
    | .lbu => IO.println s!"    {res} = LBU {v 0}, {imm}"
    -- memory: stores (mem[base + imm] ← value; operands: value, base)
    | .sd  => IO.println s!"    SD {v 0}, {v 1}, {imm}"
    | .sw  => IO.println s!"    SW {v 0}, {v 1}, {imm}"
    | .sh  => IO.println s!"    SH {v 0}, {v 1}, {imm}"
    | .sb  => IO.println s!"    SB {v 0}, {v 1}, {imm}"
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
  -- `rv64.get_register` references a physical register (e.g. the zero register
  -- `$x0`). Copy it into a virtual register so every use -- including PHI
  -- operands, which may not be physical registers -- is valid MIR; the register
  -- allocator coalesces the copy away, leaving a direct `$x0` use in assembly.
  | .rv64 .get_register =>
    match (op.getResultTypes! ctx)[0]?.bind (physRegName? ·.val) with
    | some name => IO.println s!"    {res} = COPY {name}"
    | none => IO.println s!"    ; UNHANDLED op"
  | _ => IO.println s!"    ; UNHANDLED op"

/-- Emit a terminator operation (branch / return).  `lsuccs` gives the lowered
    successor block index for each successor position (trampolines when split). -/
def emitTerminator (ctx : IRContext OpCode) (op : OperationPtr)
    (lsuccs : Array Nat) : IO Unit := do
  let opType := op.getOpType! ctx
  let ops := getOperands ctx op
  let v := fun (i : Nat) => vreg ctx (ops[i]!)
  let succ := fun (k : Nat) => lsuccs[k]!
  -- Degenerate conditional branch with both edges collapsed to the same block
  -- (equal arguments) → unconditional jump.  Split edges have distinct lsuccs.
  if lsuccs.size == 2 && succ 0 == succ 1 then
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
partial def emitOps (ctx : IRContext OpCode) (op : OperationPtr)
    (lsuccs : Array Nat) : IO Unit := do
  match (op.get! ctx).next with
  | some n =>
    emitRegular ctx op
    emitOps ctx n lsuccs
  | none =>
    emitTerminator ctx op lsuccs

/-- The lowered successor block indices for a real block, in successor order
    (the trampoline pair when the block's branch is edge-split). -/
def loweredSuccs (ctx : IRContext OpCode) (blocks : Array BlockPtr)
    (split : Array (Option (Nat × Nat))) (bi : Nat) (term : OperationPtr) : Array Nat :=
  match split[bi]! with
  | some (t0, t1) => #[t0, t1]
  | none => Id.run do
    let mut r := #[]
    for k in 0...term.getNumSuccessors! ctx do
      r := r.push (bbOf blocks (term.getSuccessor! ctx k).id)
    return r

/-- Emit one real basic block: label, successors, PHIs, then instructions. -/
def emitBlock (ctx : IRContext OpCode) (blocks : Array BlockPtr)
    (split : Array (Option (Nat × Nat)))
    (preds : Array (Array (Nat × Array ValuePtr))) (bi : Nat) : IO Unit := do
  let b := blocks[bi]!
  IO.println s!"  bb.{bi}:"
  match (b.get! ctx).firstOp with
  | none => pure ()
  | some f =>
    let term := lastOp ctx f
    let lsuccs := loweredSuccs ctx blocks split bi term
    -- successors line: distinct lowered successor indices, in order
    if !lsuccs.isEmpty then
      let mut sis : List Nat := []
      for si in lsuccs do
        if !sis.contains si then sis := sis ++ [si]
      let parts := sis.map (fun si => s!"%bb.{si}")
      IO.println s!"    successors: {String.intercalate ", " parts}"
    -- block arguments → PHI (or COPY for a single predecessor)
    let np := b.getNumArguments! ctx
    if np != 0 then
      let plist := preds[bi]!
      -- A block with no predecessors is the entry block, so its arguments are
      -- the function arguments: bind them to the RISC-V integer argument
      -- registers (a0-a7 = x10-x17) per the standard calling convention, so
      -- the allocated code is actually callable from ABI-conforming code.
      if plist.size == 0 then
        let regs := (List.range np).map (fun i => s!"$x{10 + i}")
        IO.println s!"    liveins: {String.intercalate ", " regs}"
      for ai in 0...np do
        let name := s!"%arg{b.id}_{ai}"
        if plist.size == 0 then
          IO.println s!"    {name}:gpr = COPY $x{10 + ai}"
        else if plist.size == 1 then
          let (_, vals) := plist[0]!
          IO.println s!"    {name}:gpr = COPY {vreg ctx (vals[ai]!)}"
        else
          let parts := plist.toList.map (fun (pbi, vals) => s!"{vreg ctx (vals[ai]!)}, %bb.{pbi}")
          IO.println s!"    {name}:gpr = PHI {String.intercalate ", " parts}"
    emitOps ctx f lsuccs

/-- Emit a trampoline block: an unconditional jump to its target. -/
def emitTrampoline (t : Nat) (s : Nat) : IO Unit := do
  IO.println s!"  bb.{t}:"
  IO.println s!"    successors: %bb.{s}"
  IO.println s!"    PseudoBR %bb.{s}"

/-- Print a full MIR module for the given `main` function. -/
def printMIR (ctx : IRContext OpCode) (funcOp : OperationPtr) : IO Unit := do
  let allBlocks := collectBlocks ctx (FunctionOpInterface.getEntryBlock? funcOp ctx)
  -- Drop blocks unreachable from the entry: a real codegen prunes them, and
  -- they break MIR liveness (their values aren't dominated by any real path).
  let reach :=
    if allBlocks.isEmpty then []
    else reachable ctx allBlocks [(allBlocks[0]!).id]
  let blocks := allBlocks.filter (fun b => reach.contains b.id)
  let plan := planEdges ctx blocks
  -- Entry-block arguments are the function arguments; they live in the RISC-V
  -- integer argument registers a0-a7 (x10-x17). Declare them on the stub IR
  -- signature and as MIR liveins so the register allocator keeps them there.
  let nargs := match blocks[0]? with
    | some b => b.getNumArguments! ctx
    | none => 0
  let params := String.intercalate ", " ((List.range nargs).map (fun i => s!"i64 %a{i}"))
  IO.println "--- |"
  IO.println s!"  define i64 @main({params}) #0 \{"
  IO.println "    ret i64 0"
  IO.println "  }"
  IO.println "  attributes #0 = { \"target-features\"=\"+m,+zba,+zbb,+zbs,+zbc,+zbkb,+zicond\" }"
  IO.println "..."
  IO.println "---"
  IO.println "name:            main"
  IO.println "tracksRegLiveness: true"
  if nargs != 0 then
    IO.println "liveins:"
    for i in 0...nargs do
      IO.println s!"  - \{ reg: '$x{10 + i}' }"
  IO.println "body:             |"
  for bi in 0...blocks.size do
    if bi != 0 then IO.println ""
    emitBlock ctx blocks plan.split plan.preds bi
  for tr in plan.tramps do
    IO.println ""
    emitTrampoline tr.1 tr.2
  IO.println "..."

end Veir.MIRPrinter
