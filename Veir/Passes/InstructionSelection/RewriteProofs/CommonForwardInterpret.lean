import Veir.IR.WellFormed
import Veir.Rewriter.WfRewriter
import Veir.Dominance
import Veir.Passes.Matching
import Veir.Verifier
import Veir.Passes.InstructionSelection.Common
import Veir.Interpreter

/-!
# Forward interpretation lemmas for instruction-selection rewrite proofs

This file collects `interpretOp_forward` specializations tailored to the operations that show up in
RISC-V instruction-selection lowerings. Each lemma fixes the shape of a specific op (cast-to-register,
cast-back, and unary register-to-register `riscv` ops) and reduces its one-step interpretation to a
concrete result binding, so the surrounding rewrite proofs can reason about semantics without
unfolding the interpreter by hand.
-/

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {rawCtx rawCtx' : IRContext OpInfo} {ctx ctx' : WfIRContext OpInfo}

/-- Cast-to-register specialization of `interpretOp_forward`: `castOp` is a
`builtin.unrealized_conversion_cast` with single operand `v` (holding an `i{bw}` value `x`) and a
single `!riscv.reg` result. Interpreting it always succeeds, leaves memory untouched, binds the
result to `.reg (LLVM.Int.toReg x)`, and leaves every non-result value unchanged. -/
theorem interpretOp_castToReg_forward
    {ctx : WfIRContext OpCode} {castOp : OperationPtr} {state : InterpreterState ctx}
    {inBounds : castOp.InBounds ctx.raw} {v : ValuePtr} {rt : RegisterType} {hIsTy}
    {bw : Nat} {x : Data.LLVM.Int bw}
    (hType : castOp.getOpType! ctx.raw = .builtin .unrealized_conversion_cast)
    (hOperands : castOp.getOperands! ctx.raw = #[v])
    (hResTypes : castOp.getResultTypes! ctx.raw = #[⟨.registerType rt, hIsTy⟩])
    (hVal : state.variables.getVar? v = some (.int bw x)) :
    ∃ state', interpretOp castOp state inBounds = some (.ok (state', none)) ∧
      state'.memory = state.memory ∧
      state'.variables.getVar? (ValuePtr.opResult (castOp.getResult 0))
        = some (.reg (LLVM.Int.toReg x)) ∧
      (∀ v', v' ∉ castOp.getResults! ctx.raw →
        state'.variables.getVar? v' = state.variables.getVar? v') := by
  obtain ⟨state', hI, hMem, hVar⟩ :=
    interpretOp_forward (op := castOp) (state := state) (inBounds := inBounds)
      (vals := #[.int bw x]) (results := #[.reg (LLVM.Int.toReg x)]) (mem' := state.memory)
      (by simp [VariableState.getOperandValues, hOperands, hVal])
      (by simp only [OperationPtr.interpret]
          rw [hType]
          simp [hResTypes, interpretOp', pure, Interp])
      (by simp [RuntimeValue.ArrayConforms, hResTypes, RuntimeValue.Conforms])
  grind

/-- Cast-back specialization of `interpretOp_forward`, symmetric to
`interpretOp_castToReg_forward`: `castOp` is a `builtin.unrealized_conversion_cast` with single
operand `v` (holding a register value `r`) and a single `i{bw}` result. Interpreting it always
succeeds, leaves memory untouched, binds the result to `.int bw (RISCV.Reg.toInt r bw)`, and
leaves every non-result value unchanged. -/
theorem interpretOp_castBack_forward
    {ctx : WfIRContext OpCode} {castOp : OperationPtr} {state : InterpreterState ctx}
    {inBounds : castOp.InBounds ctx.raw} {v : ValuePtr} {intTy : IntegerType} {hIsTy}
    {r : Data.RISCV.Reg}
    (hType : castOp.getOpType! ctx.raw = .builtin .unrealized_conversion_cast)
    (hOperands : castOp.getOperands! ctx.raw = #[v])
    (hResTypes : castOp.getResultTypes! ctx.raw = #[⟨.integerType intTy, hIsTy⟩])
    (hVal : state.variables.getVar? v = some (.reg r)) :
    ∃ state', interpretOp castOp state inBounds = some (.ok (state', none)) ∧
      state'.memory = state.memory ∧
      state'.variables.getVar? (ValuePtr.opResult (castOp.getResult 0))
        = some (.int intTy.bitwidth (RISCV.Reg.toInt r intTy.bitwidth)) ∧
      (∀ v', v' ∉ castOp.getResults! ctx.raw →
        state'.variables.getVar? v' = state.variables.getVar? v') := by
  obtain ⟨state', hI, hMem, hVar⟩ :=
    interpretOp_forward (op := castOp) (state := state) (inBounds := inBounds)
      (vals := #[.reg r])
      (results := #[.int intTy.bitwidth (RISCV.Reg.toInt r intTy.bitwidth)])
      (mem' := state.memory)
      (by simp [VariableState.getOperandValues, hOperands, hVal])
      (by simp only [OperationPtr.interpret]
          rw [hType]
          simp [hResTypes, interpretOp', pure, Interp])
      (by simp [RuntimeValue.ArrayConforms, hResTypes, RuntimeValue.Conforms])
  grind

/-- Binary register-to-register `riscv` op specialization of `interpretOp_forward`: `theOp` is any
`riscv` op `rop` whose interpretation maps two register operands `r₁`, `r₂` to `f r₁ r₂`
(hypothesis `hSem`, discharged by `rfl` at each concrete opcode; note the interpreter applies the
data-level op as `RISCV.op op2 op1`, so `f` is typically `fun r₁ r₂ => RISCV.op r₂ r₁`), with a
single `!riscv.reg` result. Interpreting it always succeeds, leaves memory untouched, binds the
result to `.reg (f r₁ r₂)`, and leaves every non-result value unchanged. This covers
`riscv.add`/`sub`/`mul`/`div`/`rem`/`sll`/`srl` and their `W`/unsigned variants, as well as
`riscv.andn`/`orn`/`xnor`. -/
theorem interpretOp_riscv_binaryReg_forward
    {ctx : WfIRContext OpCode} {rop : Riscv} {theOp : OperationPtr} {state : InterpreterState ctx}
    {inBounds : theOp.InBounds ctx.raw} {v₁ v₂ : ValuePtr} {rt : RegisterType} {hIsTy}
    {r₁ r₂ : Data.RISCV.Reg} {f : Data.RISCV.Reg → Data.RISCV.Reg → Data.RISCV.Reg}
    (hSem : ∀ (props : HasDialectOpInfo.propertiesOf rop) (resultTypes : Array TypeAttr)
        (blockOperands : Array BlockPtr) (mem : MemoryState),
        Riscv.interpretOp' rop props resultTypes #[.reg r₁, .reg r₂] blockOperands mem
          = some (.ok (#[.reg (f r₁ r₂)], mem, none)))
    (hType : theOp.getOpType! ctx.raw = .riscv rop)
    (hOperands : theOp.getOperands! ctx.raw = #[v₁, v₂])
    (hResTypes : theOp.getResultTypes! ctx.raw = #[⟨.registerType rt, hIsTy⟩])
    (hVal₁ : state.variables.getVar? v₁ = some (.reg r₁))
    (hVal₂ : state.variables.getVar? v₂ = some (.reg r₂)) :
    ∃ state', interpretOp theOp state inBounds = some (.ok (state', none)) ∧
      state'.memory = state.memory ∧
      state'.variables.getVar? (ValuePtr.opResult (theOp.getResult 0))
        = some (.reg (f r₁ r₂)) ∧
      (∀ v', v' ∉ theOp.getResults! ctx.raw →
        state'.variables.getVar? v' = state.variables.getVar? v') := by
  obtain ⟨state', hI, hMem, hVal⟩ :=
    interpretOp_forward (op := theOp) (state := state) (inBounds := inBounds)
      (vals := #[.reg r₁, .reg r₂]) (results := #[.reg (f r₁ r₂)]) (mem' := state.memory)
      (by simp [VariableState.getOperandValues, hOperands, hVal₁, hVal₂])
      (by simp only [OperationPtr.interpret]
          rw [hType]
          simp [interpretOp', hSem, Interp])
      (by simp [RuntimeValue.ArrayConforms, hResTypes, RuntimeValue.Conforms])
  grind

/-- Binary integer `llvm` op specialization of `interpretOp_forward`: `theOp` is an `llvm` op
`lop` whose interpretation maps two `i{bw}` operands to `.int bw (f x y props)` (hypothesis
`hSem`), with a single `i{bw}` result. Interpreting it always succeeds, leaves memory untouched,
binds the result, and leaves every non-result value unchanged. This is the LLVM-dialect analogue
of `interpretOp_riscv_binaryReg_forward`, needed when a *combine* (rather than a lowering) emits
an `llvm` operation — e.g. `mulo_by_2_unsigned_signed`, which emits `llvm.add`. -/
theorem interpretOp_llvm_binaryInt_forward
    {ctx : WfIRContext OpCode} {lop : Llvm} {theOp : OperationPtr} {state : InterpreterState ctx}
    {inBounds : theOp.InBounds ctx.raw} {v₁ v₂ : ValuePtr} {it : IntegerType} {hIsTy}
    {props : HasDialectOpInfo.propertiesOf (OpCode.llvm lop)}
    {x y : Data.LLVM.Int it.bitwidth}
    {f : Data.LLVM.Int it.bitwidth → Data.LLVM.Int it.bitwidth → Data.LLVM.Int it.bitwidth}
    (hSem : ∀ (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr)
        (mem : MemoryState),
        Llvm.interpretOp' lop props resultTypes
            #[.int it.bitwidth x, .int it.bitwidth y] blockOperands mem
          = some (.ok (#[.int it.bitwidth (f x y)], mem, none)))
    (hType : theOp.getOpType! ctx.raw = .llvm lop)
    (hProps : theOp.getProperties! ctx.raw (.llvm lop) = props)
    (hOperands : theOp.getOperands! ctx.raw = #[v₁, v₂])
    (hResTypes : theOp.getResultTypes! ctx.raw = #[⟨.integerType it, hIsTy⟩])
    (hVal₁ : state.variables.getVar? v₁ = some (.int it.bitwidth x))
    (hVal₂ : state.variables.getVar? v₂ = some (.int it.bitwidth y)) :
    ∃ state', interpretOp theOp state inBounds = some (.ok (state', none)) ∧
      state'.memory = state.memory ∧
      state'.variables.getVar? (ValuePtr.opResult (theOp.getResult 0))
        = some (.int it.bitwidth (f x y)) ∧
      (∀ v', v' ∉ theOp.getResults! ctx.raw →
        state'.variables.getVar? v' = state.variables.getVar? v') := by
  obtain ⟨state', hI, hMem, hVal⟩ :=
    interpretOp_forward (op := theOp) (state := state) (inBounds := inBounds)
      (vals := #[.int it.bitwidth x, .int it.bitwidth y])
      (results := #[.int it.bitwidth (f x y)]) (mem' := state.memory)
      (by simp [VariableState.getOperandValues, hOperands, hVal₁, hVal₂])
      (by simp only [OperationPtr.interpret]
          rw [hType]
          simp only [interpretOp', hProps]
          simp [hSem, Interp])
      (by simp [RuntimeValue.ArrayConforms, hResTypes, RuntimeValue.Conforms])
  grind

/-- Comparison `llvm.icmp` specialization of `interpretOp_forward`: `theOp` is an `llvm.icmp`
whose two `i{bw}` operands map to a single `i1` result `f x y` (hypothesis `hSem`). Unlike
`interpretOp_llvm_binaryInt_forward`, the operand width `it` and the result width (`1`) differ,
so this is the mixed-width analogue needed by the `not_cmp_fold` combine, which emits an
`llvm.icmp`. -/
theorem interpretOp_llvm_icmp_forward
    {ctx : WfIRContext OpCode} {theOp : OperationPtr} {state : InterpreterState ctx}
    {inBounds : theOp.InBounds ctx.raw} {v₁ v₂ : ValuePtr} {it i1t : IntegerType} {hIsTy}
    {props : propertiesOf (.llvm .icmp)}
    {x y : Data.LLVM.Int it.bitwidth}
    {f : Data.LLVM.Int it.bitwidth → Data.LLVM.Int it.bitwidth → Data.LLVM.Int 1}
    (hi1 : i1t.bitwidth = 1)
    (hSem : ∀ (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr)
        (mem : MemoryState),
        Llvm.interpretOp' .icmp props resultTypes
            #[.int it.bitwidth x, .int it.bitwidth y] blockOperands mem
          = some (.ok (#[.int 1 (f x y)], mem, none)))
    (hType : theOp.getOpType! ctx.raw = .llvm .icmp)
    (hProps : theOp.getProperties! ctx.raw (.llvm .icmp) = props)
    (hOperands : theOp.getOperands! ctx.raw = #[v₁, v₂])
    (hResTypes : theOp.getResultTypes! ctx.raw = #[⟨.integerType i1t, hIsTy⟩])
    (hVal₁ : state.variables.getVar? v₁ = some (.int it.bitwidth x))
    (hVal₂ : state.variables.getVar? v₂ = some (.int it.bitwidth y)) :
    ∃ state', interpretOp theOp state inBounds = some (.ok (state', none)) ∧
      state'.memory = state.memory ∧
      state'.variables.getVar? (ValuePtr.opResult (theOp.getResult 0))
        = some (.int 1 (f x y)) ∧
      (∀ v', v' ∉ theOp.getResults! ctx.raw →
        state'.variables.getVar? v' = state.variables.getVar? v') := by
  obtain ⟨state', hI, hMem, hVal⟩ :=
    interpretOp_forward (op := theOp) (state := state) (inBounds := inBounds)
      (vals := #[.int it.bitwidth x, .int it.bitwidth y])
      (results := #[.int 1 (f x y)]) (mem' := state.memory)
      (by simp [VariableState.getOperandValues, hOperands, hVal₁, hVal₂])
      (by simp only [OperationPtr.interpret]
          rw [hType]
          simp only [interpretOp', hProps]
          simp [hSem, Interp])
      (by simp [RuntimeValue.ArrayConforms, hResTypes, RuntimeValue.Conforms, hi1])
  grind

/-- Unary integer `llvm` op specialization of `interpretOp_forward`: `theOp` is an `llvm` op `lop`
whose interpretation maps a single `i{srcW}` operand to `.int resType.bitwidth (f x)` (hypothesis
`hSem`), with a single `i{resType}` result — a *width-changing* unary op (`zext`/`sext`). Needed by
the `match_selects` combine, which emits an `llvm.zext`/`sext` of the `select`'s `i1` condition. -/
theorem interpretOp_llvm_unaryInt_forward
    {ctx : WfIRContext OpCode} {lop : Llvm} {theOp : OperationPtr} {state : InterpreterState ctx}
    {inBounds : theOp.InBounds ctx.raw} {v : ValuePtr} {srcType resType : IntegerType} {hIsTy}
    {props : HasDialectOpInfo.propertiesOf (OpCode.llvm lop)}
    {x : Data.LLVM.Int srcType.bitwidth}
    {f : Data.LLVM.Int srcType.bitwidth → Data.LLVM.Int resType.bitwidth}
    (hSem : ∀ (blockOperands : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' lop props #[⟨.integerType resType, hIsTy⟩]
            #[.int srcType.bitwidth x] blockOperands mem
          = some (.ok (#[.int resType.bitwidth (f x)], mem, none)))
    (hType : theOp.getOpType! ctx.raw = .llvm lop)
    (hProps : theOp.getProperties! ctx.raw (.llvm lop) = props)
    (hOperands : theOp.getOperands! ctx.raw = #[v])
    (hResTypes : theOp.getResultTypes! ctx.raw = #[⟨.integerType resType, hIsTy⟩])
    (hVal : state.variables.getVar? v = some (.int srcType.bitwidth x)) :
    ∃ state', interpretOp theOp state inBounds = some (.ok (state', none)) ∧
      state'.memory = state.memory ∧
      state'.variables.getVar? (ValuePtr.opResult (theOp.getResult 0))
        = some (.int resType.bitwidth (f x)) ∧
      (∀ v', v' ∉ theOp.getResults! ctx.raw →
        state'.variables.getVar? v' = state.variables.getVar? v') := by
  obtain ⟨state', hI, hMem, hVal⟩ :=
    interpretOp_forward (op := theOp) (state := state) (inBounds := inBounds)
      (vals := #[.int srcType.bitwidth x])
      (results := #[.int resType.bitwidth (f x)]) (mem' := state.memory)
      (by simp [VariableState.getOperandValues, hOperands, hVal])
      (by simp only [OperationPtr.interpret]
          rw [hType, hResTypes]
          simp only [interpretOp', hProps]
          simp [hSem, Interp])
      (by simp [RuntimeValue.ArrayConforms, hResTypes, RuntimeValue.Conforms])
  grind

/-- Unary register-to-register `riscv` op specialization of `interpretOp_forward`: `theOp` is any
`riscv` op `rop` whose interpretation maps a single register operand `r` to `f r` (hypothesis
`hSem`, discharged by `rfl` at each concrete opcode), with a single `!riscv.reg` result.
Interpreting it always succeeds, leaves memory untouched, binds the result to `.reg (f r)`, and
leaves every non-result value unchanged. This covers `riscv.clz`/`clzw`/`ctz`/`ctzw`/`cpop`/
`cpopw` and any future unary Zbb op. -/
theorem interpretOp_riscv_unaryReg_forward
    {ctx : WfIRContext OpCode} {rop : Riscv} {theOp : OperationPtr} {state : InterpreterState ctx}
    {inBounds : theOp.InBounds ctx.raw} {v : ValuePtr} {rt : RegisterType} {hIsTy}
    {r : Data.RISCV.Reg} {f : Data.RISCV.Reg → Data.RISCV.Reg}
    (hSem : ∀ (props : HasDialectOpInfo.propertiesOf rop) (resultTypes : Array TypeAttr)
        (blockOperands : Array BlockPtr) (mem : MemoryState),
        Riscv.interpretOp' rop props resultTypes #[.reg r] blockOperands mem
          = some (.ok (#[.reg (f r)], mem, none)))
    (hType : theOp.getOpType! ctx.raw = .riscv rop)
    (hOperands : theOp.getOperands! ctx.raw = #[v])
    (hResTypes : theOp.getResultTypes! ctx.raw = #[⟨.registerType rt, hIsTy⟩])
    (hVal : state.variables.getVar? v = some (.reg r)) :
    ∃ state', interpretOp theOp state inBounds = some (.ok (state', none)) ∧
      state'.memory = state.memory ∧
      state'.variables.getVar? (ValuePtr.opResult (theOp.getResult 0))
        = some (.reg (f r)) ∧
      (∀ v', v' ∉ theOp.getResults! ctx.raw →
        state'.variables.getVar? v' = state.variables.getVar? v') := by
  obtain ⟨state', hI, hMem, hVal⟩ :=
    interpretOp_forward (op := theOp) (state := state) (inBounds := inBounds)
      (vals := #[.reg r]) (results := #[.reg (f r)]) (mem' := state.memory)
      (by simp [VariableState.getOperandValues, hOperands, hVal])
      (by simp only [OperationPtr.interpret]
          rw [hType]
          simp [interpretOp', hSem, Interp])
      (by simp [RuntimeValue.ArrayConforms, hResTypes, RuntimeValue.Conforms])
  grind

/-- Immediate-form unary register-to-register `riscv` op specialization of `interpretOp_forward`:
`theOp` is any `riscv` op `rop` with a *fixed* property bundle `props` (typically the immediate)
whose interpretation maps a single register operand `r` to `res` (hypothesis `hSem`, discharged by
`rfl`/`simp` at each concrete opcode-and-immediate), with a single `!riscv.reg` result. Unlike
`interpretOp_riscv_unaryReg_forward`, the result depends on the op's properties, so the op's
actual property bundle is required as an input (`hProps`). Interpreting it always succeeds, leaves
memory untouched, binds the result to `.reg res`, and leaves every non-result value unchanged. This
covers the immediate forms `riscv.andi`/`ori`/`xori`/`slli`/`srli`/`srai`/`addi`/… . -/
theorem interpretOp_riscv_unaryReg_imm_forward
    {ctx : WfIRContext OpCode} {rop : Riscv} {theOp : OperationPtr} {state : InterpreterState ctx}
    {inBounds : theOp.InBounds ctx.raw} {v : ValuePtr} {rt : RegisterType} {hIsTy}
    {r res : Data.RISCV.Reg} {props : HasDialectOpInfo.propertiesOf rop}
    (hSem : ∀ (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState),
        Riscv.interpretOp' rop props resultTypes #[.reg r] blockOperands mem
          = some (.ok (#[.reg res], mem, none)))
    (hType : theOp.getOpType! ctx.raw = .riscv rop)
    (hProps : theOp.getProperties! ctx.raw (.riscv rop) = props)
    (hOperands : theOp.getOperands! ctx.raw = #[v])
    (hResTypes : theOp.getResultTypes! ctx.raw = #[⟨.registerType rt, hIsTy⟩])
    (hVal : state.variables.getVar? v = some (.reg r)) :
    ∃ state', interpretOp theOp state inBounds = some (.ok (state', none)) ∧
      state'.memory = state.memory ∧
      state'.variables.getVar? (ValuePtr.opResult (theOp.getResult 0))
        = some (.reg res) ∧
      (∀ v', v' ∉ theOp.getResults! ctx.raw →
        state'.variables.getVar? v' = state.variables.getVar? v') := by
  obtain ⟨state', hI, hMem, hVal⟩ :=
    interpretOp_forward (op := theOp) (state := state) (inBounds := inBounds)
      (vals := #[.reg r]) (results := #[.reg res]) (mem' := state.memory)
      (by simp [VariableState.getOperandValues, hOperands, hVal])
      (by simp only [OperationPtr.interpret]
          rw [hType, hProps]
          simp [interpretOp', hSem, Interp])
      (by simp [RuntimeValue.ArrayConforms, hResTypes, RuntimeValue.Conforms])
  grind

/-- Byte cast-to-register specialization of `interpretOp_forward`: like `interpretOp_castToReg_forward`
but the operand holds an `i{bw}` *byte* value, cast to `.reg (LLVM.Byte.toReg x)`. -/
theorem interpretOp_castToReg_byte_forward
    {ctx : WfIRContext OpCode} {castOp : OperationPtr} {state : InterpreterState ctx}
    {inBounds : castOp.InBounds ctx.raw} {v : ValuePtr} {rt : RegisterType} {hIsTy}
    {bw : Nat} {x : Data.LLVM.Byte bw}
    (hType : castOp.getOpType! ctx.raw = .builtin .unrealized_conversion_cast)
    (hOperands : castOp.getOperands! ctx.raw = #[v])
    (hResTypes : castOp.getResultTypes! ctx.raw = #[⟨.registerType rt, hIsTy⟩])
    (hVal : state.variables.getVar? v = some (.byte bw x)) :
    ∃ state', interpretOp castOp state inBounds = some (.ok (state', none)) ∧
      state'.memory = state.memory ∧
      state'.variables.getVar? (ValuePtr.opResult (castOp.getResult 0))
        = some (.reg (LLVM.Byte.toReg x)) ∧
      (∀ v', v' ∉ castOp.getResults! ctx.raw →
        state'.variables.getVar? v' = state.variables.getVar? v') := by
  obtain ⟨state', hI, hMem, hVar⟩ :=
    interpretOp_forward (op := castOp) (state := state) (inBounds := inBounds)
      (vals := #[.byte bw x]) (results := #[.reg (LLVM.Byte.toReg x)]) (mem' := state.memory)
      (by simp [VariableState.getOperandValues, hOperands, hVal])
      (by simp only [OperationPtr.interpret]
          rw [hType]
          simp [hResTypes, interpretOp', pure, Interp])
      (by simp [RuntimeValue.ArrayConforms, hResTypes, RuntimeValue.Conforms])
  grind

/-- Byte cast-back specialization of `interpretOp_forward`: like `interpretOp_castBack_forward` but
the result has *byte* type, so the register `r` is cast to `.byte bw (RISCV.Reg.toByte r bw)`. -/
theorem interpretOp_castBack_byte_forward
    {ctx : WfIRContext OpCode} {castOp : OperationPtr} {state : InterpreterState ctx}
    {inBounds : castOp.InBounds ctx.raw} {v : ValuePtr} {byteTy : LLVM.ByteType} {hIsTy}
    {r : Data.RISCV.Reg}
    (hType : castOp.getOpType! ctx.raw = .builtin .unrealized_conversion_cast)
    (hOperands : castOp.getOperands! ctx.raw = #[v])
    (hResTypes : castOp.getResultTypes! ctx.raw = #[⟨.byteType byteTy, hIsTy⟩])
    (hVal : state.variables.getVar? v = some (.reg r)) :
    ∃ state', interpretOp castOp state inBounds = some (.ok (state', none)) ∧
      state'.memory = state.memory ∧
      state'.variables.getVar? (ValuePtr.opResult (castOp.getResult 0))
        = some (.byte byteTy.bitwidth (RISCV.Reg.toByte r byteTy.bitwidth)) ∧
      (∀ v', v' ∉ castOp.getResults! ctx.raw →
        state'.variables.getVar? v' = state.variables.getVar? v') := by
  obtain ⟨state', hI, hMem, hVar⟩ :=
    interpretOp_forward (op := castOp) (state := state) (inBounds := inBounds)
      (vals := #[.reg r])
      (results := #[.byte byteTy.bitwidth (RISCV.Reg.toByte r byteTy.bitwidth)])
      (mem' := state.memory)
      (by simp [VariableState.getOperandValues, hOperands, hVal])
      (by simp only [OperationPtr.interpret]
          rw [hType]
          simp [hResTypes, interpretOp', pure, Interp])
      (by simp [RuntimeValue.ArrayConforms, hResTypes, RuntimeValue.Conforms])
  grind
