module

public import Veir.Dialects.Builtin.Interpreter
public import Veir.Data.Casting
public import Veir.PatternRewriter.Puddle.Simp
import Veir.Data.RISCV.Reg.Lemmas
import all Veir.Dialects.Builtin.Interpreter
import all Veir.Data.Casting

/-!
# Builtin CTree interpreter lemmas

Simulation lemmas for `builtin.unrealized_conversion_cast` between values and registers.
-/

namespace Veir

open _root_.CTree

public section

variable {EIn : Type} {E : EIn → Type} [ErrorE -< E] [UBE -< E]
variable {C'In : Type} {C' : C'In → Type}
variable (f : Array RuntimeValue × MemoryState × Option ControlFlowAction →
  Array RuntimeValue × MemoryState × Option ControlFlowAction → Prop)
variable (after : (Array RuntimeValue × MemoryState × Option ControlFlowAction) →
    CTree E FreezeC (Array RuntimeValue × MemoryState × Option ControlFlowAction))
variable (other : CTree E C' (Array RuntimeValue × MemoryState × Option ControlFlowAction))

/-!
# Unfolding lemmas for builtin.unrealized_conversion_cast interpreter

These lemmas unfold the interpreter for each of the input/output type combinations.
-/

@[simp, puddle]
theorem Builtin.interpretUnrealizedConversionCastCTree_reg_int
    {bw : Nat} (value : Data.LLVM.Int bw) (mem : MemoryState) :
  Builtin.interpretUnrealizedConversionCastCTree (E := E) #[TypeAttr.of RegisterType { }]
    #[RuntimeValue.int bw value] mem =
    (Builtin.intToRegCTree value >>= fun reg => pure (#[RuntimeValue.reg reg], mem, none)) := by
  simp [Builtin.interpretUnrealizedConversionCastCTree, Attribute.of_def,
    -Attribute.registerType_eq_of]

@[simp, puddle]
theorem Builtin.interpretUnrealizedConversionCastCTree_reg_byte
    {bw : Nat} (value : Data.LLVM.Byte bw) (mem : MemoryState) :
  Builtin.interpretUnrealizedConversionCastCTree (E := E) #[TypeAttr.of RegisterType { }]
    #[RuntimeValue.byte bw value] mem =
    (Builtin.byteToRegCTree value >>= fun reg => pure (#[RuntimeValue.reg reg], mem, none)) := by
  simp [Builtin.interpretUnrealizedConversionCastCTree, Attribute.of_def,
    -Attribute.registerType_eq_of]

@[simp, puddle]
theorem Builtin.interpretUnrealizedConversionCastCTree_int_reg
    (type : IntegerType) (value : Data.RISCV.Reg) (mem : MemoryState) :
  Builtin.interpretUnrealizedConversionCastCTree (E := E) #[TypeAttr.of IntegerType type]
    #[RuntimeValue.reg value] mem =
    pure (#[RuntimeValue.int type.bitwidth (RISCV.Reg.toInt value type.bitwidth)], mem, none) := by
  simp [Builtin.interpretUnrealizedConversionCastCTree, Attribute.of_def,
    -Attribute.integerType_eq_of]

@[simp, puddle]
theorem Builtin.interpretUnrealizedConversionCastCTree_byte_reg
    (type : LLVM.ByteType) (value : Data.RISCV.Reg) (mem : MemoryState) :
  Builtin.interpretUnrealizedConversionCastCTree (E := E) #[TypeAttr.of LLVM.ByteType type]
    #[RuntimeValue.reg value] mem =
    pure (#[RuntimeValue.byte type.bitwidth (RISCV.Reg.toByte value type.bitwidth)], mem, none) := by
  simp [Builtin.interpretUnrealizedConversionCastCTree, Attribute.of_def,
    -Attribute.byteType_eq_of]

@[simp, puddle]
theorem Builtin.interpretUnrealizedConversionCastCTree_reg_addr
    (value : Data.LLVM.Ptr) (mem : MemoryState) :
  Builtin.interpretUnrealizedConversionCastCTree (E := E) #[TypeAttr.of RegisterType { }]
    #[RuntimeValue.addr value] mem =
    (Builtin.intToRegCTree value.toInt >>= fun reg => pure (#[RuntimeValue.reg reg], mem, none)) := by
  cases h : value.toInt <;>
    simp [Builtin.interpretUnrealizedConversionCastCTree, Builtin.intToRegCTree,
      Attribute.of_def, -Attribute.registerType_eq_of, h]

@[simp, puddle]
theorem Builtin.interpretUnrealizedConversionCastCTree_addr_reg
    (type : LLVM.PointerType) (value : Data.RISCV.Reg) (mem : MemoryState) :
  Builtin.interpretUnrealizedConversionCastCTree (E := E) #[TypeAttr.of LLVM.PointerType type]
    #[RuntimeValue.reg value] mem =
    pure (#[RuntimeValue.addr (mem.ptrFromInt (.val value.val))], mem, none) := by
  simp [Builtin.interpretUnrealizedConversionCastCTree, Attribute.of_def,
    -Attribute.llvmPointerType_eq_of]

/-!
# Simplification lemmas for unrealized_conversion_cast simulation

These lemmas simplify simulations involving `builtin.unrealized_conversion_cast`.
-/

variable [HasUB EIn]

/-- Casting an integer to a register preserves defined bits; poison permits any register value. -/
@[puddle]
theorem CTree.Sim.bind_interpretUnrealizedConversionCastCTree_reg_int_iff
  (a : Data.LLVM.Int bitwidth) (memory : MemoryState) :
  (CTree.Sim f
    (CTree.bind
      (Builtin.interpretUnrealizedConversionCastCTree #[TypeAttr.of RegisterType { }]
        #[RuntimeValue.int bitwidth a] memory) after)
    other) ↔
  (∀ (value : Data.RISCV.Reg), (∀ bits, a = .val bits → value.val = bits.setWidth 64) →
    CTree.Sim f (after (#[.reg value], memory, none)) other) := by
  simp only [Builtin.interpretUnrealizedConversionCastCTree_reg_int, Builtin.intToRegCTree]
  cases a with
  | val bits =>
    simp <;> grind [cases Data.RISCV.Reg]
  | poison =>
    simp only [CTree.choose_def, Subeffect.mapEff_eq_self, Subeffect.mapCont, Subeffect.map_eq_self,
      id_eq, CTree.ret_pure, CTree.tau_def, bind_pure_comp, Functor.map, CTree.CTree.bind_tau,
      SumE.eq_inr, CTree.bind_pure, Function.comp_apply, Sim.tau_l, reduceCtorEq, false_implies,
      implies_true, forall_const]
    grind [cases Data.RISCV.Reg]

/-- Casting a byte to a register preserves defined bits and resolves poisoned bits before resizing. -/
@[puddle]
theorem CTree.Sim.bind_interpretUnrealizedConversionCastCTree_reg_byte_iff
  (a : Data.LLVM.Byte bitwidth) (memory : MemoryState) :
  CTree.Sim (E := E) (C := FreezeC) (C' := C') f
    (CTree.bind
      (Builtin.interpretUnrealizedConversionCastCTree (E := E) #[TypeAttr.of RegisterType { }]
        #[RuntimeValue.byte bitwidth a] memory) after)
    other ↔
  ∀ (x : BitVec bitwidth),
    CTree.Sim (E := E) (C := FreezeC) (C' := C') f
      (after (#[.reg ⟨
        BitVec.setWidth 64 a.val ||| BitVec.setWidth 64 a.poison &&& BitVec.setWidth 64 x
      ⟩], memory, none)) other := by
  simp only [Builtin.interpretUnrealizedConversionCastCTree_reg_byte, Builtin.byteToRegCTree,
    Data.LLVM.Byte.fillPoison, bind_pure_comp]
  by_cases h : a.poison = 0#bitwidth
  · simp [h]
  simp [Functor.map, h, CTree.choose_def, CTree.tau_def]

/-- Casting a register to an integer deterministically resizes its bits. -/
@[puddle]
theorem CTree.Sim.bind_interpretUnrealizedConversionCastCTree_int_reg_iff
  (type : IntegerType) (a : Data.RISCV.Reg) (memory : MemoryState) :
  CTree.Sim (E := E) (C := FreezeC) (C' := C') f
    (CTree.bind
      (Builtin.interpretUnrealizedConversionCastCTree (E := E) #[TypeAttr.of IntegerType type]
        #[RuntimeValue.reg a] memory) after)
    other ↔
  CTree.Sim (E := E) (C := FreezeC) (C' := C') f
    (after (#[.int type.bitwidth (.val (a.val.setWidth type.bitwidth))], memory, none))
    other := by
  simp [RISCV.Reg.toInt]

/-- Casting a register to a byte deterministically resizes its bits and produces no poison. -/
@[puddle]
theorem CTree.Sim.bind_interpretUnrealizedConversionCastCTree_byte_reg_iff
  (type : LLVM.ByteType) (a : Data.RISCV.Reg) (memory : MemoryState) :
  CTree.Sim (E := E) (C := FreezeC) (C' := C') f
    (CTree.bind
      (Builtin.interpretUnrealizedConversionCastCTree (E := E) #[TypeAttr.of LLVM.ByteType type]
        #[RuntimeValue.reg a] memory) after)
    other ↔
  CTree.Sim (E := E) (C := FreezeC) (C' := C') f
    (after (#[.byte type.bitwidth ⟨a.val.setWidth type.bitwidth, 0, by simp⟩], memory, none))
    other := by
  simp [RISCV.Reg.toByte]

/-- Casting an address to a register preserves its bits; poison permits any register value. -/
@[puddle]
theorem CTree.Sim.bind_interpretUnrealizedConversionCastCTree_reg_addr_iff
  (a : Data.LLVM.Ptr) (memory : MemoryState) :
  CTree.Sim (E := E) (C := FreezeC) (C' := C') f
    (CTree.bind
      (Builtin.interpretUnrealizedConversionCastCTree (E := E) #[TypeAttr.of RegisterType { }]
        #[RuntimeValue.addr a] memory) after)
    other ↔
  ∀ (value : Data.RISCV.Reg),
    (∀ bits, a.toInt = .val bits → value.val = bits) →
    CTree.Sim (E := E) (C := FreezeC) (C' := C') f
      (after (#[.reg value], memory, none)) other := by
  simpa using CTree.Sim.bind_interpretUnrealizedConversionCastCTree_reg_int_iff
    f after other a.toInt memory

/-- Casting a register to an address decodes its bits using the current memory state. -/
@[puddle]
theorem CTree.Sim.bind_interpretUnrealizedConversionCastCTree_addr_reg_iff
  (type : LLVM.PointerType) (a : Data.RISCV.Reg) (memory : MemoryState) :
  CTree.Sim (E := E) (C := FreezeC) (C' := C') f
    (CTree.bind
      (Builtin.interpretUnrealizedConversionCastCTree (E := E) #[TypeAttr.of LLVM.PointerType type]
        #[RuntimeValue.reg a] memory) after)
    other ↔
  CTree.Sim (E := E) (C := FreezeC) (C' := C') f
    (after (#[.addr (memory.ptrFromInt (.val a.val))], memory, none)) other := by
  simp

end

end Veir
