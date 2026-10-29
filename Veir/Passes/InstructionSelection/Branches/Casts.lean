module

public import Veir.Passes.InstructionSelection.RISCV64Branches

import Veir.Interpreter.Refinement.Lemmas
import Veir.Dialects.GMIR.Lemmas
import Veir.Dialects.RISCV_Cf.Lemmas
import Veir.Dialects.RV64.Lemmas

public section

/-!
# Casting a value to a register and back

The branch lowering passes a value along a branch as a register. The value is
cast to a register in front of the branch and back to its type at the start of
the successor. This file gives the meaning of the two casts, shows that a value
of a type that `roundTrips` is refined by its round trip, and shows that the
RISC-V branch on the registers takes the successor that the gMIR branch takes.

A pointer fits a register too, but it travels as its address and comes back as
the pointer that the memory decodes that address to, which refines it only when
the pointer's object owns its address. `roundTrips` leaves pointers out, so the
proof does not cover a branch that passes one.
-/

open Veir.Data

namespace Veir

/--
  Whether a value of type `type` is refined by its round trip through a register:
  an integer or a byte that fits one.
-/
def roundTrips (type : TypeAttr) : Bool :=
  match type.val with
  | .integerType _ | .byteType _ => fitsRegister type
  | _ => false

theorem fitsRegister_of_roundTrips {type : TypeAttr} (h : roundTrips type) :
    fitsRegister type := by
  obtain ⟨attr, hattr⟩ := type
  cases attr <;> simp_all [roundTrips]

/--
  The register that `builtin.unrealized_conversion_cast` turns an integer or a
  byte into.
-/
def RuntimeValue.toReg? : RuntimeValue → Option RISCV.Reg
  | .int _ value => some (LLVM.Int.toReg value)
  | .byte _ value => some (LLVM.Byte.toReg value)
  | _ => none

/--
  The integer or byte of type `type` that `builtin.unrealized_conversion_cast`
  turns a register into.
-/
def RuntimeValue.ofReg? (type : TypeAttr) (reg : RISCV.Reg) : Option RuntimeValue :=
  match type.val with
  | .integerType intType => some (.int intType.bitwidth (RISCV.Reg.toInt reg intType.bitwidth))
  | .byteType byteType => some (.byte byteType.bitwidth (RISCV.Reg.toByte reg byteType.bitwidth))
  | _ => none

/-- A cast to a register computes `toReg?`. -/
theorem interpretOp'_cast_toReg {value : RuntimeValue} {reg : RISCV.Reg} {mem : MemoryState}
    (hReg : value.toReg? = some reg)
    (properties : propertiesOf (OpCode.builtin .unrealized_conversion_cast))
    (successors : Array BlockPtr) :
    interpretOp' (.builtin .unrealized_conversion_cast) properties #[RegisterType.mk] #[value]
      successors mem = .ok (#[.reg reg], mem, none) := by
  cases value <;> grind [RuntimeValue.toReg?, interpretOp']

/-- A cast from a register computes `ofReg?`. -/
theorem interpretOp'_cast_ofReg {type : TypeAttr} {reg : RISCV.Reg} {value : RuntimeValue}
    {mem : MemoryState} (hValue : RuntimeValue.ofReg? type reg = some value)
    (properties : propertiesOf (OpCode.builtin .unrealized_conversion_cast))
    (successors : Array BlockPtr) :
    interpretOp' (.builtin .unrealized_conversion_cast) properties #[type] #[.reg reg]
      successors mem = .ok (#[value], mem, none) := by
  obtain ⟨attr, hattr⟩ := type
  cases attr <;> grind [RuntimeValue.ofReg?, interpretOp']

/-- A value of a type that `roundTrips` is cast to a register. -/
theorem RuntimeValue.toReg?_eq_some_of_roundTrips {type : TypeAttr} {value : RuntimeValue}
    (hRoundTrips : roundTrips type) (hConforms : value.Conforms type) :
    ∃ reg, value.toReg? = some reg := by
  obtain ⟨attr, hattr⟩ := type
  cases attr <;> simp only [roundTrips, Bool.false_eq_true] at hRoundTrips
  all_goals cases value <;> simp only [Conforms] at hConforms <;> exact ⟨_, rfl⟩

/--
  A value of a type that `roundTrips` is refined by what comes back from the
  register it is cast to, and what comes back is of its type.
-/
theorem RuntimeValue.isRefinedBy_ofReg?_of_toReg? {type : TypeAttr} {value : RuntimeValue}
    {reg : RISCV.Reg} (hRoundTrips : roundTrips type) (hConforms : value.Conforms type)
    (hReg : value.toReg? = some reg) :
    ∃ value', RuntimeValue.ofReg? type reg = some value' ∧ value ⊒ value' ∧
      value'.Conforms type := by
  obtain ⟨attr, hattr⟩ := type
  cases attr <;> simp [roundTrips] at hRoundTrips
  all_goals
    cases value <;> simp only [Conforms] at hConforms <;> subst hConforms
    simp only [toReg?, Option.some.injEq] at hReg
    subst hReg
    exact ⟨_, rfl, by grind [RuntimeValue.isRefinedBy], rfl⟩

/--
  A value of a type that `roundTrips` is refined by its round trip through a
  register, even when the value that is cast is only a refinement of it.
-/
theorem RuntimeValue.isRefinedBy_ofReg?_toReg? {type : TypeAttr} {source target : RuntimeValue}
    (hRoundTrips : roundTrips type) (hConforms : source.Conforms type)
    (hRefined : source ⊒ target) :
    ∃ reg value, target.toReg? = some reg ∧ RuntimeValue.ofReg? type reg = some value ∧
      source ⊒ value ∧ value.Conforms type := by
  have hTarget := hConforms.of_isRefinedBy hRefined
  obtain ⟨reg, hReg⟩ := toReg?_eq_some_of_roundTrips hRoundTrips hTarget
  obtain ⟨value, hValue, hRefined', hConforms'⟩ :=
    isRefinedBy_ofReg?_of_toReg? hRoundTrips hTarget hReg
  exact ⟨reg, value, hReg, hValue, RuntimeValue.isRefinedBy_trans hRefined hRefined',
    hConforms'⟩

/-! ## The branches -/

/--
  `target` holds the registers that the values `source` are cast to, where the
  value that is cast may be a refinement of the source value.
-/
structure RegistersOf (source target : Array RuntimeValue) : Prop where
  /-- There is one register per value. -/
  size_eq : source.size = target.size
  /-- The register at `i` is the cast of a refinement of the value at `i`. -/
  get : ∀ i, i < source.size → ∃ value reg,
    source[i]! ⊒ value ∧ value.toReg? = some reg ∧ target[i]! = .reg reg

/-- No value has no register. -/
theorem RegistersOf.empty : RegistersOf #[] #[] := ⟨rfl, by simp⟩

/-- One more value and the register it is cast to. -/
theorem RegistersOf.push {source target : Array RuntimeValue} (h : RegistersOf source target)
    {s value : RuntimeValue} {reg : RISCV.Reg} (hRefined : s ⊒ value)
    (hReg : value.toReg? = some reg) :
    RegistersOf (source.push s) (target.push (.reg reg)) := by
  refine ⟨by simp [h.size_eq], fun i hi => ?_⟩
  grind [h.size_eq, h.get]

theorem RegistersOf.extract {source target : Array RuntimeValue}
    (h : RegistersOf source target) (start stop : Nat) :
    RegistersOf (source.extract start stop) (target.extract start stop) := by
  refine ⟨by simp [h.size_eq], fun i hi => ?_⟩
  have := h.get (start + i) (by simp at hi; omega)
  grind [h.size_eq]

theorem RegistersOf.extract_from {source target : Array RuntimeValue}
    (h : RegistersOf source target) (start : Nat) :
    RegistersOf (source.extract start) (target.extract start) :=
  h.size_eq ▸ h.extract start source.size

/--
  The registers of the operands of a branch after the first are those after the
  first two registers, in any range of positions.
-/
theorem RegistersOf.extract_shift {source target : Array RuntimeValue}
    (h : RegistersOf (source.extract 1) (target.extract 2)) (start stop : Nat) :
    RegistersOf (source.extract (start + 1) (stop + 1)) (target.extract (start + 2) (stop + 2)) := by
  have hSize := h.size_eq
  simp only [Array.size_extract] at hSize
  refine ⟨by simp; omega, fun i hi => ?_⟩
  simp only [Array.size_extract] at hi
  obtain ⟨value, reg, h₁, h₂, h₃⟩ := h.get (start + i) (by simp; omega)
  refine ⟨value, reg, ?_, h₂, ?_⟩
  · rw [getElem!_pos _ _ (by simp; omega)] at h₁ ⊢
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h₁
  · rw [getElem!_pos _ _ (by simp; omega)] at h₃ ⊢
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h₃

/-- `riscv_cf.branch` on the registers of the operands of a `g_br` branches like it. -/
theorem interpretOp'_br_registers
    {properties resultTypes operands successors mem results mem' action}
    (h : interpretOp' (.gmir .g_br) properties resultTypes operands successors mem =
      .ok (results, mem', action))
    {registers : Array RuntimeValue} (hRegisters : RegistersOf operands registers)
    (properties' : propertiesOf (OpCode.riscv_cf .branch)) (resultTypes' : Array TypeAttr) :
    ∃ values values' dest, results = #[] ∧ mem' = mem ∧
      action = some (.branch values dest) ∧
      interpretOp' (.riscv_cf .branch) properties' resultTypes' registers successors mem =
        .ok (#[], mem, some (.branch values' dest)) ∧
      RegistersOf values values' := by
  obtain ⟨dest, rfl, rfl, rfl, rfl⟩ := interpretOp'_gmir_g_br_eq_ok_iff.mp h
  exact ⟨operands, registers, dest, rfl, rfl, rfl, interpretOp'_riscv_cf_branch,
    hRegisters⟩

/--
  `riscv_cf.bnez` on the registers of the operands of a `g_brcond` branches like
  it, for a condition that fits a register. A poison condition is undefined
  behaviour in the source, so there is nothing to show for it.
-/
theorem interpretOp'_brcond_registers
    {properties resultTypes operands successors mem results mem' action}
    (h : interpretOp' (.gmir .g_brcond) properties resultTypes operands successors mem =
      .ok (results, mem', action))
    (hWidth : ∀ w x, operands[0]? = some (.int w x) → w ≤ 64)
    {registers : Array RuntimeValue} (hRegisters : RegistersOf operands registers)
    (properties' : propertiesOf (OpCode.riscv_cf .bnez)) (resultTypes' : Array TypeAttr)
    (hSizes : properties'.operandSegmentSizes = properties.operandSegmentSizes) :
    ∃ values values' dest, results = #[] ∧ mem' = mem ∧
      action = some (.branch values dest) ∧
      interpretOp' (.riscv_cf .bnez) properties' resultTypes' registers successors mem =
        .ok (#[], mem, some (.branch values' dest)) ∧
      RegistersOf values values' := by
  obtain ⟨destTrue, destFalse, w, cond, n, rfl, hCond, hSize, rfl, rfl, rfl⟩ :=
    interpretOp'_gmir_g_brcond_eq_ok_iff.mp h
  have hw := hWidth w _ hCond
  obtain ⟨hLt, hOperand⟩ := Array.getElem?_eq_some_iff.mp hCond
  obtain ⟨value, reg, hRefined, hReg, hRegister⟩ := hRegisters.get 0 hLt
  rw [getElem!_pos operands 0 hLt, hOperand, RuntimeValue.int_val_isRefinedBy_iff]
    at hRefined
  subst hRefined
  simp only [RuntimeValue.toReg?, Option.some.injEq] at hReg
  have hRegister' : registers[0]? = some (.reg reg) := by
    rw [← hRegister]; exact Array.getElem?_eq_some_getElem! _ _ (hRegisters.size_eq ▸ hLt)
  have hRegVal : reg.val = cond.zeroExtend 64 := by simp [← hReg, val_toReg]
  have hCondIff : reg.val ≠ 0#64 ↔ cond ≠ 0 := by
    rw [hRegVal]
    constructor
    · intro h hc; exact h (by simp [hc])
    · intro h hc
      apply h
      apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat hc
      simp only [BitVec.toNat_setWidth, BitVec.toNat_zero] at this ⊢
      rwa [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le cond.isLt (Nat.pow_le_pow_right (by omega) hw))]
        at this
  rw [interpretOp'_riscv_cf_bnez hRegister' (hSizes ▸ hSize)]
  by_cases hc : cond = 0
  · simp only [hCondIff, hc, ne_eq, not_true_eq_false, ↓reduceIte]
    exact ⟨_, _, destFalse, trivial, trivial, rfl, rfl, hRegisters.extract_from _⟩
  · simp only [hCondIff, hc, ne_eq, not_false_eq_true, ↓reduceIte]
    exact ⟨_, _, destTrue, trivial, trivial, rfl, rfl, hRegisters.extract _ _⟩

/-- A compare-and-branch takes its first successor when `compareHolds` holds of its registers. -/
theorem interpretOp'_riscv_cf_compare {branch : CondBranch}
    (hBranch : branch.val ∈ [Riscv_Cf.beq, .bne, .blt, .bge, .bltu, .bgeu])
    {segments : DenseArrayAttr} {resultTypes : Array TypeAttr} {operands : Array RuntimeValue}
    {lhs rhs : RISCV.Reg} {n : Int} {destTrue destFalse : BlockPtr} {mem : MemoryState}
    (hLhs : operands[0]? = some (.reg lhs)) (hRhs : operands[1]? = some (.reg rhs))
    (hSize : segments.values[2]? = some n) :
    interpretOp' (.riscv_cf branch.val) (cast branch.property.symm (⟨segments⟩ : RISCVBrProperties))
        resultTypes operands #[destTrue, destFalse] mem =
      .ok (#[], mem, some (if compareHolds branch.val lhs.val rhs.val then
        .branch (operands.extract 2 (n.toNat + 2)) destTrue
        else .branch (operands.extract (n.toNat + 2) operands.size) destFalse)) := by
  obtain ⟨op, hOp⟩ := branch
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hBranch
  rcases hBranch with rfl | rfl | rfl | rfl | rfl | rfl
  · show interpretOp' (.riscv_cf .beq) (⟨segments⟩ : RISCVBrProperties) resultTypes operands
      #[destTrue, destFalse] mem = _
    rw [interpretOp'_riscv_cf_beq hLhs hRhs hSize]; simp
  · show interpretOp' (.riscv_cf .bne) (⟨segments⟩ : RISCVBrProperties) resultTypes operands
      #[destTrue, destFalse] mem = _
    rw [interpretOp'_riscv_cf_bne hLhs hRhs hSize]; simp
  · show interpretOp' (.riscv_cf .blt) (⟨segments⟩ : RISCVBrProperties) resultTypes operands
      #[destTrue, destFalse] mem = _
    rw [interpretOp'_riscv_cf_blt hLhs hRhs hSize]; simp
  · show interpretOp' (.riscv_cf .bge) (⟨segments⟩ : RISCVBrProperties) resultTypes operands
      #[destTrue, destFalse] mem = _
    rw [interpretOp'_riscv_cf_bge hLhs hRhs hSize]; simp
  · show interpretOp' (.riscv_cf .bltu) (⟨segments⟩ : RISCVBrProperties) resultTypes operands
      #[destTrue, destFalse] mem = _
    rw [interpretOp'_riscv_cf_bltu hLhs hRhs hSize]; simp
  · show interpretOp' (.riscv_cf .bgeu) (⟨segments⟩ : RISCVBrProperties) resultTypes operands
      #[destTrue, destFalse] mem = _
    rw [interpretOp'_riscv_cf_bgeu hLhs hRhs hSize]; simp

/--
  The compare-and-branch that replaces a `g_brcond` on the result `cond` of
  `g_icmp lhs rhs` branches like it. Its first two registers hold `value l` and
  `value r`, the registers of the compared values or `x0`, and the rest are those
  of the operands of the `g_brcond` after its condition. The compared values are
  integers of 64 bits, and a constant `rhs` holds its value. A poison condition is
  undefined behaviour in the source, so there is nothing to show for it.
-/
theorem interpretOp'_brcond_compare_registers
    {properties resultTypes operands successors mem results mem' action}
    (h : interpretOp' (.gmir .g_brcond) properties resultTypes operands successors mem =
      .ok (results, mem', action))
    {icmpProperties : propertiesOf (OpCode.gmir .g_icmp)} {icmpResultTypes icmpSuccessors icmpMem
      icmpMem' icmpAction} {a b cond : RuntimeValue}
    (hIcmp : interpretOp' (.gmir .g_icmp) icmpProperties icmpResultTypes #[a, b] icmpSuccessors
      icmpMem = .ok (#[cond], icmpMem', icmpAction))
    (hCond : operands[0]? = some cond)
    (hWidth : ∀ w x, a = .int w x → w = 64)
    {lhs rhs : ValuePtr} {rhsConstant : Option Int} {value : Option ValuePtr → BitVec 64}
    (hNone : value none = 0)
    (hLhs : ∀ x, a = .int 64 (.val x) → value (some lhs) = x)
    (hRhs : ∀ y, b = .int 64 (.val y) → value (some rhs) = y)
    (hConstant : ∀ c, rhsConstant = some c → b = .int 64 (.val (BitVec.ofInt 64 c)))
    {registers : Array RuntimeValue}
    (hReg₀ : registers[0]? = some (.reg ⟨value
      (compareBranch icmpProperties.predicate lhs rhs rhsConstant).2.1⟩))
    (hReg₁ : registers[1]? = some (.reg ⟨value
      (compareBranch icmpProperties.predicate lhs rhs rhsConstant).2.2⟩))
    (hRegisters : RegistersOf (operands.extract 1) (registers.extract 2))
    {segments : DenseArrayAttr}
    (hSegments : segments.values = #[1] ++ properties.operandSegmentSizes.values)
    (resultTypes' : Array TypeAttr) :
    ∃ values values' dest, results = #[] ∧ mem' = mem ∧
      action = some (.branch values dest) ∧
      interpretOp' (.riscv_cf (compareBranch icmpProperties.predicate lhs rhs rhsConstant).1.val)
        (cast (compareBranch icmpProperties.predicate lhs rhs rhsConstant).1.property.symm
          (⟨segments⟩ : RISCVBrProperties)) resultTypes' registers successors mem =
        .ok (#[], mem, some (.branch values' dest)) ∧
      RegistersOf values values' := by
  obtain ⟨destTrue, destFalse, w, c, n, rfl, hC, hSize, rfl, rfl, rfl⟩ :=
    interpretOp'_gmir_g_brcond_eq_ok_iff.mp h
  obtain ⟨bw, x, y, w', c', hOps, hRes, -, -, hHolds⟩ := interpretOp'_gmir_g_icmp_eq_ok hIcmp
  obtain ⟨rfl, rfl⟩ : a = .int bw x ∧ b = .int bw y := by simpa using hOps
  obtain rfl : cond = .int w' c' := by simpa using hRes
  obtain ⟨rfl, hc⟩ : w' = w ∧ c' ≍ (Data.LLVM.Int.val c : Data.LLVM.Int w) := by
    rw [hCond] at hC; simpa using hC
  obtain rfl := eq_of_heq hc
  obtain ⟨x', y', rfl, rfl, hIff⟩ := hHolds c rfl
  obtain rfl := hWidth bw _ rfl
  have hHolds' := compareBranch_holds (pred := icmpProperties.predicate) (lhs := lhs) (rhs := rhs)
    (rhsConstant := rhsConstant) hNone (fun k hk => by
      have := hConstant k hk
      simp only [RuntimeValue.int.injEq, heq_eq_eq, true_and, Data.LLVM.Int.val.injEq] at this
      rw [hRhs y' rfl, this])
  rw [hLhs x' rfl, hRhs y' rfl] at hHolds'
  have hSize' : segments.values[2]? = some n := by
    rw [hSegments]
    simpa [Array.getElem?_append_right] using hSize
  have hLen : 1 ≤ operands.size := by
    have := (Array.getElem?_eq_some_iff.mp hC).1; omega
  have hLen' : registers.size = operands.size + 1 := by
    have := hRegisters.size_eq
    have := (Array.getElem?_eq_some_iff.mp hReg₁).1
    simp only [Array.size_extract] at *
    omega
  rw [interpretOp'_riscv_cf_compare compareBranch_mem hReg₀ hReg₁ hSize', hHolds']
  by_cases hc : c = 0
  · have hEval : Data.LLVM.IntPred.eval icmpProperties.predicate x' y' = false := by
      simpa [hc] using hIff
    simp only [hEval, hc, ne_eq, not_true_eq_false, ↓reduceIte, Bool.false_eq_true]
    refine ⟨_, _, destFalse, trivial, trivial, rfl, rfl, ?_⟩
    have := hRegisters.extract_shift n.toNat (operands.size - 1)
    rwa [Nat.sub_add_cancel hLen, show operands.size - 1 + 2 = registers.size by omega] at this
  · have hEval : Data.LLVM.IntPred.eval icmpProperties.predicate x' y' = true := hIff.mp hc
    simp only [hEval, hc, ne_eq, not_false_eq_true, ↓reduceIte]
    exact ⟨_, _, destTrue, trivial, trivial, rfl, rfl,
      by simpa using hRegisters.extract_shift 0 n.toNat⟩

end Veir
