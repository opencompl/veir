module
import all Veir.IR.Attribute
public meta import Veir.PatternRewriter.Puddle.Definitions
public meta import Veir.PatternRewriter.Puddle.Validity
public import Veir.PatternRewriter.Puddle.CTreeValidity
public import Veir.PatternRewriter.Puddle.CTreeSymbolicValidity
public import Veir.PatternRewriter.Puddle.CTreeProgramValidity
public import Veir.Passes.InstructionSelection.RISCV64
public import Veir.Dialects.LLVM.Interpreter
import Veir.Passes.InstructionSelection.RISCV64CTreeSemantics
import all Veir.Passes.InstructionSelection.RISCV64
import all Veir.OpCode
import all Veir.PatternRewriter.Puddle.CTreeValidity
import all Veir.PatternRewriter.Puddle.Validity
import all Veir.GlobalOpInfo
import all Veir.Dialects.LLVM.Interpreter
import all Veir.Interpreter.Basic
import all Veir.Dialects.LLVM.OpInfo
import all Veir.Dialects.Builtin.OpInfo
import Veir.Passes.InstructionSelection.Proofs
import all Veir.Dialects.RISCV.OpInfo
import all Veir.Interpreter.CTree
import all Veir.Interpreter.Interp
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.Refinement
import all Veir.Data.RISCV.Reg.Basic
import all Veir.Data.Casting


namespace Veir
set_option linter.unusedSimpArgs false
open Puddle Puddle.CTree

namespace Puddle.CTree
@[simp] theorem CanInterpretTo.llvm_add (w : Nat) (ty : IntegerType)
    (p : propertiesOf (OpCode.llvm .add)) (x y : Data.LLVM.Int w)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .add) p #[TypeAttr.of IntegerType ty]
      #[.int w x, .int w y] r ↔
    r = .ok #[.int w (Data.LLVM.Int.add x y p.nsw p.nuw)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree]
  cases r <;> simp
@[simp] theorem CanInterpretTo.llvm_sub (w : Nat) (ty : IntegerType)
    (p : propertiesOf (OpCode.llvm .sub)) (x y : Data.LLVM.Int w)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .sub) p #[TypeAttr.of IntegerType ty]
      #[.int w x, .int w y] r ↔
    r = .ok #[.int w (Data.LLVM.Int.sub x y p.nsw p.nuw)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree]
  cases r <;> simp

@[simp] theorem CanInterpretTo.llvm_mul (w : Nat) (ty : IntegerType)
    (p : propertiesOf (OpCode.llvm .mul)) (x y : Data.LLVM.Int w)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .mul) p #[TypeAttr.of IntegerType ty]
      #[.int w x, .int w y] r ↔
    r = .ok #[.int w (Data.LLVM.Int.mul x y p.nsw p.nuw)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree]
  cases r <;> simp

@[simp] theorem CanInterpretTo.llvm_and (w : Nat) (ty : IntegerType)
    (p : propertiesOf (OpCode.llvm .and)) (x y : Data.LLVM.Int w)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .and) p #[TypeAttr.of IntegerType ty]
      #[.int w x, .int w y] r ↔
    r = .ok #[.int w (Data.LLVM.Int.and x y)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree]
  cases r <;> simp

@[simp] theorem CanInterpretTo.llvm_or (w : Nat) (ty : IntegerType)
    (p : propertiesOf (OpCode.llvm .or)) (x y : Data.LLVM.Int w)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .or) p #[TypeAttr.of IntegerType ty]
      #[.int w x, .int w y] r ↔
    r = .ok #[.int w (Data.LLVM.Int.or x y p.disjoint)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree]
  cases r <;> simp

@[simp] theorem CanInterpretTo.llvm_xor (w : Nat) (ty : IntegerType)
    (p : propertiesOf (OpCode.llvm .xor)) (x y : Data.LLVM.Int w)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .xor) p #[TypeAttr.of IntegerType ty]
      #[.int w x, .int w y] r ↔
    r = .ok #[.int w (Data.LLVM.Int.xor x y)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree]
  cases r <;> simp

@[simp] theorem CanInterpretTo.llvm_intr__smax (w : Nat) (ty : IntegerType)
    (p : propertiesOf (OpCode.llvm .intr__smax)) (x y : Data.LLVM.Int w)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .intr__smax) p #[TypeAttr.of IntegerType ty]
      #[.int w x, .int w y] r ↔
    r = .ok #[.int w (Data.LLVM.Int.smax x y)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree]
  cases r <;> simp

@[simp] theorem CanInterpretTo.llvm_intr__smin (w : Nat) (ty : IntegerType)
    (p : propertiesOf (OpCode.llvm .intr__smin)) (x y : Data.LLVM.Int w)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .intr__smin) p #[TypeAttr.of IntegerType ty]
      #[.int w x, .int w y] r ↔
    r = .ok #[.int w (Data.LLVM.Int.smin x y)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree]
  cases r <;> simp

@[simp] theorem CanInterpretTo.llvm_intr__umax (w : Nat) (ty : IntegerType)
    (p : propertiesOf (OpCode.llvm .intr__umax)) (x y : Data.LLVM.Int w)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .intr__umax) p #[TypeAttr.of IntegerType ty]
      #[.int w x, .int w y] r ↔
    r = .ok #[.int w (Data.LLVM.Int.umax x y)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree]
  cases r <;> simp

@[simp] theorem CanInterpretTo.llvm_intr__umin (w : Nat) (ty : IntegerType)
    (p : propertiesOf (OpCode.llvm .intr__umin)) (x y : Data.LLVM.Int w)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .intr__umin) p #[TypeAttr.of IntegerType ty]
      #[.int w x, .int w y] r ↔
    r = .ok #[.int w (Data.LLVM.Int.umin x y)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree]
  cases r <;> simp

@[simp] theorem CanInterpretTo.riscv_add (x y : Data.RISCV.Reg)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .add) () #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.reg x, .reg y] r ↔ r = .ok #[.reg (Data.RISCV.add y x)] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

@[simp] theorem CanInterpretTo.riscv_addw (x y : Data.RISCV.Reg)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .addw) () #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.reg x, .reg y] r ↔ r = .ok #[.reg (Data.RISCV.addw y x)] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

@[simp] theorem CanInterpretTo.riscv_sub (x y : Data.RISCV.Reg)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .sub) () #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.reg x, .reg y] r ↔ r = .ok #[.reg (Data.RISCV.sub y x)] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

@[simp] theorem CanInterpretTo.riscv_subw (x y : Data.RISCV.Reg)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .subw) () #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.reg x, .reg y] r ↔ r = .ok #[.reg (Data.RISCV.subw y x)] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

@[simp] theorem CanInterpretTo.riscv_mul (x y : Data.RISCV.Reg)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .mul) () #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.reg x, .reg y] r ↔ r = .ok #[.reg (Data.RISCV.mul y x)] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

@[simp] theorem CanInterpretTo.riscv_mulw (x y : Data.RISCV.Reg)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .mulw) () #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.reg x, .reg y] r ↔ r = .ok #[.reg (Data.RISCV.mulw y x)] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

@[simp] theorem CanInterpretTo.riscv_div (x y : Data.RISCV.Reg)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .div) () #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.reg x, .reg y] r ↔ r = .ok #[.reg (Data.RISCV.div y x)] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

@[simp] theorem CanInterpretTo.riscv_divw (x y : Data.RISCV.Reg)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .divw) () #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.reg x, .reg y] r ↔ r = .ok #[.reg (Data.RISCV.divw y x)] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

@[simp] theorem CanInterpretTo.riscv_divu (x y : Data.RISCV.Reg)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .divu) () #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.reg x, .reg y] r ↔ r = .ok #[.reg (Data.RISCV.divu y x)] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

@[simp] theorem CanInterpretTo.riscv_divuw (x y : Data.RISCV.Reg)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .divuw) () #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.reg x, .reg y] r ↔ r = .ok #[.reg (Data.RISCV.divuw y x)] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

@[simp] theorem CanInterpretTo.riscv_rem (x y : Data.RISCV.Reg)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .rem) () #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.reg x, .reg y] r ↔ r = .ok #[.reg (Data.RISCV.rem y x)] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

@[simp] theorem CanInterpretTo.riscv_remw (x y : Data.RISCV.Reg)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .remw) () #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.reg x, .reg y] r ↔ r = .ok #[.reg (Data.RISCV.remw y x)] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

@[simp] theorem CanInterpretTo.riscv_remu (x y : Data.RISCV.Reg)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .remu) () #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.reg x, .reg y] r ↔ r = .ok #[.reg (Data.RISCV.remu y x)] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

@[simp] theorem CanInterpretTo.riscv_remuw (x y : Data.RISCV.Reg)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .remuw) () #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.reg x, .reg y] r ↔ r = .ok #[.reg (Data.RISCV.remuw y x)] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

@[simp] theorem CanInterpretTo.riscv_and (x y : Data.RISCV.Reg)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .and) () #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.reg x, .reg y] r ↔ r = .ok #[.reg (Data.RISCV.and y x)] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

@[simp] theorem CanInterpretTo.riscv_or (x y : Data.RISCV.Reg)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .or) () #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.reg x, .reg y] r ↔ r = .ok #[.reg (Data.RISCV.or y x)] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

@[simp] theorem CanInterpretTo.riscv_xor (x y : Data.RISCV.Reg)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .xor) () #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.reg x, .reg y] r ↔ r = .ok #[.reg (Data.RISCV.xor y x)] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

@[simp] theorem CanInterpretTo.riscv_max (x y : Data.RISCV.Reg)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .max) () #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.reg x, .reg y] r ↔ r = .ok #[.reg (Data.RISCV.max y x)] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

@[simp] theorem CanInterpretTo.riscv_min (x y : Data.RISCV.Reg)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .min) () #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.reg x, .reg y] r ↔ r = .ok #[.reg (Data.RISCV.min y x)] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

@[simp] theorem CanInterpretTo.riscv_maxu (x y : Data.RISCV.Reg)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .maxu) () #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.reg x, .reg y] r ↔ r = .ok #[.reg (Data.RISCV.maxu y x)] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

@[simp] theorem CanInterpretTo.riscv_minu (x y : Data.RISCV.Reg)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .minu) () #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.reg x, .reg y] r ↔ r = .ok #[.reg (Data.RISCV.minu y x)] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

@[simp] theorem CanInterpretTo.riscv_rol (x y : Data.RISCV.Reg)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .rol) () #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.reg x, .reg y] r ↔ r = .ok #[.reg (Data.RISCV.rol y x)] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

@[simp] theorem CanInterpretTo.riscv_rolw (x y : Data.RISCV.Reg)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .rolw) () #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.reg x, .reg y] r ↔ r = .ok #[.reg (Data.RISCV.rolw y x)] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

@[simp] theorem CanInterpretTo.riscv_ror (x y : Data.RISCV.Reg)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .ror) () #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.reg x, .reg y] r ↔ r = .ok #[.reg (Data.RISCV.ror y x)] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

@[simp] theorem CanInterpretTo.riscv_rorw (x y : Data.RISCV.Reg)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .rorw) () #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.reg x, .reg y] r ↔ r = .ok #[.reg (Data.RISCV.rorw y x)] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl
@[simp] theorem CanInterpretTo.riscv_sextb (x : Data.RISCV.Reg)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .sextb) () #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.reg x] r ↔ r = .ok #[.reg (Data.RISCV.sextb x)] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

@[simp] theorem CanInterpretTo.riscv_sexth (x : Data.RISCV.Reg)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .sexth) () #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.reg x] r ↔ r = .ok #[.reg (Data.RISCV.sexth x)] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

@[simp] theorem CanInterpretTo.riscv_sextw (x : Data.RISCV.Reg)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .sextw) () #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.reg x] r ↔ r = .ok #[.reg (Data.RISCV.sextw x)] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

@[simp] theorem CanInterpretTo.riscv_zextb (x : Data.RISCV.Reg)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .zextb) () #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.reg x] r ↔ r = .ok #[.reg (Data.RISCV.zextb x)] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

@[simp] theorem CanInterpretTo.riscv_zexth (x : Data.RISCV.Reg)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .zexth) () #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.reg x] r ↔ r = .ok #[.reg (Data.RISCV.zexth x)] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

@[simp] theorem CanInterpretTo.riscv_zextw (x : Data.RISCV.Reg)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .zextw) () #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.reg x] r ↔ r = .ok #[.reg (Data.RISCV.zextw x)] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

@[simp] theorem CanInterpretTo.llvm_intr__fshl (w : Nat) (ty : IntegerType)
    (p : propertiesOf (OpCode.llvm .intr__fshl)) (x y : Data.LLVM.Int w)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .intr__fshl) p #[TypeAttr.of IntegerType ty]
      #[.int w x, .int w x, .int w y] r ↔
    r = .ok #[.int w (Data.LLVM.Int.fshl x x y)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree]
  cases r <;> simp

@[simp] theorem CanInterpretTo.llvm_intr__fshr (w : Nat) (ty : IntegerType)
    (p : propertiesOf (OpCode.llvm .intr__fshr)) (x y : Data.LLVM.Int w)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .intr__fshr) p #[TypeAttr.of IntegerType ty]
      #[.int w x, .int w x, .int w y] r ↔
    r = .ok #[.int w (Data.LLVM.Int.fshr x x y)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree]
  cases r <;> simp

theorem CanInterpretTo.llvm_sdiv_source (w : Nat) (ty : IntegerType)
    (p : propertiesOf (OpCode.llvm .sdiv)) (x y : Data.LLVM.Int w) :
    CanInterpretTo (.llvm .sdiv) p #[TypeAttr.of IntegerType ty] #[.int w x, .int w y]
      (if Data.LLVM.Int.isSignedDivisionUB x y then .ub none
       else .ok #[.int w (Data.LLVM.Int.sdiv x y p.exact)]) := by
  cases h : Data.LLVM.Int.isSignedDivisionUB x y <;>
    simp [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree, h]
  intro memory
  simp only [Functor.map, bind, Veir.ub, CTree.CTree.trigger, CTree.CTree.bind_vis]
  exact .ub

theorem CanInterpretTo.llvm_udiv_source (w : Nat) (ty : IntegerType)
    (p : propertiesOf (OpCode.llvm .udiv)) (x y : Data.LLVM.Int w) :
    CanInterpretTo (.llvm .udiv) p #[TypeAttr.of IntegerType ty] #[.int w x, .int w y]
      (if Data.LLVM.Int.isUnsignedDivisionUB y then .ub none
       else .ok #[.int w (Data.LLVM.Int.udiv x y p.exact)]) := by
  cases h : Data.LLVM.Int.isUnsignedDivisionUB y <;>
    simp [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree, h]
  intro memory
  simp only [Functor.map, bind, Veir.ub, CTree.CTree.trigger, CTree.CTree.bind_vis]
  exact .ub

theorem CanInterpretTo.llvm_srem_source (w : Nat) (ty : IntegerType)
    (p : propertiesOf (OpCode.llvm .srem)) (x y : Data.LLVM.Int w) :
    CanInterpretTo (.llvm .srem) p #[TypeAttr.of IntegerType ty] #[.int w x, .int w y]
      (if Data.LLVM.Int.isSignedDivisionUB x y then .ub none
       else .ok #[.int w (Data.LLVM.Int.srem x y)]) := by
  cases h : Data.LLVM.Int.isSignedDivisionUB x y <;>
    simp [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree, h]
  intro memory
  simp only [Functor.map, bind, Veir.ub, CTree.CTree.trigger, CTree.CTree.bind_vis]
  exact .ub

theorem CanInterpretTo.llvm_urem_source (w : Nat) (ty : IntegerType)
    (p : propertiesOf (OpCode.llvm .urem)) (x y : Data.LLVM.Int w) :
    CanInterpretTo (.llvm .urem) p #[TypeAttr.of IntegerType ty] #[.int w x, .int w y]
      (if Data.LLVM.Int.isUnsignedDivisionUB y then .ub none
       else .ok #[.int w (Data.LLVM.Int.urem x y)]) := by
  cases h : Data.LLVM.Int.isUnsignedDivisionUB y <;>
    simp [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree, h]
  intro memory
  simp only [Functor.map, bind, Veir.ub, CTree.CTree.trigger, CTree.CTree.bind_vis]
  exact .ub

theorem CanInterpretTo.refines_int_result {op : OpCode} {p : propertiesOf op}
    {types : Array TypeAttr} {args : Array RuntimeValue} {w : Nat}
    {isUB : Bool} {value target : Data.LLVM.Int w}
    (hsource : CanInterpretTo op p types args
      (if isUB then .ub none else .ok #[.int w value]))
    (hvalue : value ⊒ target) :
    ∃ source, CanInterpretTo op p types args source ∧
      Interp.isRefinedBy RuntimeValue.arrayIsRefinedBy source (.ok #[.int w target]) := by
  refine ⟨_, hsource, ?_⟩
  cases isUB
  · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
      RuntimeValue.isRefinedBy] using hvalue
  · simp [Interp.isRefinedBy]

end Puddle.CTree

set_option trace.profiler true in
theorem add64_pattern_valid : Puddle.CTree.Pattern.Valid add64_pattern := by
  unfold add64_pattern lowerBinary
  provePuddleValid program sym =>
    rintro _ ty rfl hwidth
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x y p
    cases ty with | mk bw sign =>
      dsimp at hwidth
      subst bw
      puddleStep sym [CanInterpretTo.cast_int_val']
      intro xChoice
      puddleStep sym [CanInterpretTo.cast_int_val']
      intro yChoice
      puddleStep sym [CanInterpretTo.riscv_add]
      puddleStep sym [CanInterpretTo.cast_reg_int]
      refine ⟨_, (CanInterpretTo.llvm_add 64 ⟨64, sign⟩ p x y _).mpr rfl, ?_⟩
      simp
      cases x <;> cases y <;> simp [Data.LLVM.Int.add, Id.run, pure, RISCV.Reg.toInt,
        Data.RISCV.add]
      · simp [RuntimeValue.isRefinedBy, isRefinedBy]
        grind
      · simp [RuntimeValue.isRefinedBy, isRefinedBy]
      · simp [RuntimeValue.isRefinedBy, isRefinedBy]
      · simp [RuntimeValue.isRefinedBy, isRefinedBy]

theorem add32_pattern_valid : Puddle.CTree.Pattern.Valid add32_pattern := by
  unfold add32_pattern lowerBinary
  provePuddleValid program sym =>
    rintro _ ty rfl hwidth
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x y p
    cases ty with | mk bw sign =>
      dsimp at hwidth
      subst bw
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.riscv_addw]
      puddleStep sym [CanInterpretTo.cast_reg_int]
      have hplain := Data.RISCV.addw_refinement (x := x) (y := y)
      cases x <;> cases y <;> simp [RuntimeValue.arrayIsRefinedBy_cons, Interp.isRefinedBy,
        RuntimeValue.isRefinedBy]
      all_goals simp [Id.run, pure, Pure.pure, Data.LLVM.Int.add, isRefinedBy, RISCV.Reg.toInt, Data.RISCV.addw,
        RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, LLVM.Int.toReg] at hplain ⊢
      all_goals
        intros
        subst_vars
        try simp [hplain, RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, isRefinedBy]
      all_goals grind only [isRefinedBy]

theorem sub64_pattern_valid : Puddle.CTree.Pattern.Valid sub64_pattern := by
  unfold sub64_pattern lowerBinary
  provePuddleValid program sym =>
    rintro _ ty rfl hwidth
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x y p
    cases ty with | mk bw sign =>
      dsimp at hwidth
      subst bw
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.riscv_sub]
      puddleStep sym [CanInterpretTo.cast_reg_int]
      have hplain := Data.RISCV.sub_refinement (x := x) (y := y)
      cases x <;> cases y <;> simp [RuntimeValue.arrayIsRefinedBy_cons, Interp.isRefinedBy,
        RuntimeValue.isRefinedBy]
      all_goals simp [Id.run, pure, Pure.pure, Data.LLVM.Int.sub, isRefinedBy, RISCV.Reg.toInt, Data.RISCV.sub,
        RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, LLVM.Int.toReg] at hplain ⊢
      all_goals
        intros
        subst_vars
        try simp [hplain, RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, isRefinedBy]
      all_goals grind only [isRefinedBy]

theorem sub32_pattern_valid : Puddle.CTree.Pattern.Valid sub32_pattern := by
  unfold sub32_pattern lowerBinary
  provePuddleValid program sym =>
    rintro _ ty rfl hwidth
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x y p
    cases ty with | mk bw sign =>
      dsimp at hwidth
      subst bw
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.riscv_subw]
      puddleStep sym [CanInterpretTo.cast_reg_int]
      have hplain := Data.RISCV.subw_refinement (x := x) (y := y)
      cases x <;> cases y <;> simp [RuntimeValue.arrayIsRefinedBy_cons, Interp.isRefinedBy,
        RuntimeValue.isRefinedBy]
      all_goals simp [Id.run, pure, Pure.pure, Data.LLVM.Int.sub, isRefinedBy, RISCV.Reg.toInt, Data.RISCV.subw,
        RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, LLVM.Int.toReg] at hplain ⊢
      all_goals
        intros
        subst_vars
        try simp [hplain, RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, isRefinedBy]
      all_goals grind only [isRefinedBy]

theorem mul64_pattern_valid : Puddle.CTree.Pattern.Valid mul64_pattern := by
  unfold mul64_pattern lowerBinary
  provePuddleValid program sym =>
    rintro _ ty rfl hwidth
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x y p
    cases ty with | mk bw sign =>
      dsimp at hwidth
      subst bw
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.riscv_mul]
      puddleStep sym [CanInterpretTo.cast_reg_int]
      have hplain := Data.RISCV.mul_refinement (x := x) (y := y)
      cases x <;> cases y <;> simp [RuntimeValue.arrayIsRefinedBy_cons, Interp.isRefinedBy,
        RuntimeValue.isRefinedBy]
      all_goals simp [Id.run, pure, Pure.pure, Data.LLVM.Int.mul, isRefinedBy, RISCV.Reg.toInt, Data.RISCV.mul,
        RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, LLVM.Int.toReg] at hplain ⊢
      all_goals
        intros
        subst_vars
        try simp [hplain, RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, isRefinedBy]
      all_goals grind only [isRefinedBy]

theorem mul32_pattern_valid : Puddle.CTree.Pattern.Valid mul32_pattern := by
  unfold mul32_pattern lowerBinary
  provePuddleValid program sym =>
    rintro _ ty rfl hwidth
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x y p
    cases ty with | mk bw sign =>
      dsimp at hwidth
      subst bw
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.riscv_mulw]
      puddleStep sym [CanInterpretTo.cast_reg_int]
      have hplain := Data.RISCV.mul_refinement_32 (x := x) (y := y)
      cases x <;> cases y <;> simp [RuntimeValue.arrayIsRefinedBy_cons, Interp.isRefinedBy,
        RuntimeValue.isRefinedBy]
      all_goals simp [Id.run, pure, Pure.pure, Data.LLVM.Int.mul, isRefinedBy, RISCV.Reg.toInt, Data.RISCV.mulw,
        RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, LLVM.Int.toReg] at hplain ⊢
      all_goals
        intros
        subst_vars
        try simp [hplain, RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, isRefinedBy]
      all_goals grind only [isRefinedBy]

theorem xor64_pattern_valid : Puddle.CTree.Pattern.Valid xor64_pattern := by
  unfold xor64_pattern lowerBinary
  provePuddleValid program sym =>
    rintro _ ty rfl hwidth
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x y p
    cases ty with | mk bw sign =>
      dsimp at hwidth
      subst bw
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.riscv_xor]
      puddleStep sym [CanInterpretTo.cast_reg_int]
      have hplain := Data.RISCV.xor_refinement (x := x) (y := y)
      cases x <;> cases y <;> simp [RuntimeValue.arrayIsRefinedBy_cons, Interp.isRefinedBy,
        RuntimeValue.isRefinedBy]
      all_goals simp [Id.run, pure, Pure.pure, Data.LLVM.Int.xor, isRefinedBy, RISCV.Reg.toInt, Data.RISCV.xor,
        RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, LLVM.Int.toReg] at hplain ⊢
      all_goals
        intros
        subst_vars
        try simp [hplain, RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, isRefinedBy]
      all_goals grind only [isRefinedBy]

theorem xor32_pattern_valid : Puddle.CTree.Pattern.Valid xor32_pattern := by
  unfold xor32_pattern lowerBinary
  provePuddleValid program sym =>
    rintro _ ty rfl hwidth
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x y p
    cases ty with | mk bw sign =>
      dsimp at hwidth
      subst bw
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.riscv_xor]
      puddleStep sym [CanInterpretTo.cast_reg_int]
      have hplain := Data.RISCV.xor_refinement_32 (x := x) (y := y)
      cases x <;> cases y <;> simp [RuntimeValue.arrayIsRefinedBy_cons, Interp.isRefinedBy,
        RuntimeValue.isRefinedBy]
      all_goals simp [Id.run, pure, Pure.pure, Data.LLVM.Int.xor, isRefinedBy, RISCV.Reg.toInt, Data.RISCV.xor,
        RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, LLVM.Int.toReg] at hplain ⊢
      all_goals
        intros
        subst_vars
        try simp [hplain, RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, isRefinedBy]
      all_goals grind only [isRefinedBy]

theorem smax64_pattern_valid : Puddle.CTree.Pattern.Valid smax64_pattern := by
  unfold smax64_pattern lowerBinary
  provePuddleValid program sym =>
    rintro _ ty rfl hwidth
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x y p
    cases ty with | mk bw sign =>
      dsimp at hwidth
      subst bw
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.riscv_max]
      puddleStep sym [CanInterpretTo.cast_reg_int]
      have hplain := Data.RISCV.smax_refinement (x := x) (y := y)
      cases x <;> cases y <;> simp [RuntimeValue.arrayIsRefinedBy_cons, Interp.isRefinedBy,
        RuntimeValue.isRefinedBy]
      all_goals simp [Id.run, pure, Pure.pure, Data.LLVM.Int.smax, isRefinedBy, RISCV.Reg.toInt, Data.RISCV.max,
        RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, LLVM.Int.toReg] at hplain ⊢
      all_goals
        intros
        subst_vars
        try simp [hplain, RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, isRefinedBy]
      all_goals grind only [isRefinedBy]

theorem smin64_pattern_valid : Puddle.CTree.Pattern.Valid smin64_pattern := by
  unfold smin64_pattern lowerBinary
  provePuddleValid program sym =>
    rintro _ ty rfl hwidth
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x y p
    cases ty with | mk bw sign =>
      dsimp at hwidth
      subst bw
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.riscv_min]
      puddleStep sym [CanInterpretTo.cast_reg_int]
      have hplain := Data.RISCV.smin_refinement (x := x) (y := y)
      cases x <;> cases y <;> simp [RuntimeValue.arrayIsRefinedBy_cons, Interp.isRefinedBy,
        RuntimeValue.isRefinedBy]
      all_goals simp [Id.run, pure, Pure.pure, Data.LLVM.Int.smin, isRefinedBy, RISCV.Reg.toInt, Data.RISCV.min,
        RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, LLVM.Int.toReg] at hplain ⊢
      all_goals
        intros
        subst_vars
        try simp [hplain, RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, isRefinedBy]
      all_goals grind only [isRefinedBy]

theorem smax32_pattern_valid : Puddle.CTree.Pattern.Valid smax32_pattern := by
  unfold smax32_pattern lowerBinary
  provePuddleValid program sym =>
    rintro _ ty rfl hwidth
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x y p
    cases ty with | mk bw sign =>
      dsimp at hwidth
      subst bw
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.riscv_sextw]
      puddleStep sym [CanInterpretTo.riscv_sextw]
      puddleStep sym [CanInterpretTo.riscv_max]
      puddleStep sym [CanInterpretTo.cast_reg_int]
      have hplain := Data.RISCV.smax_refinement_32 (x := x) (y := y)
      cases x <;> cases y <;> simp [RuntimeValue.arrayIsRefinedBy_cons, Interp.isRefinedBy,
        RuntimeValue.isRefinedBy]
      all_goals simp [Id.run, pure, Pure.pure, Data.LLVM.Int.smax, isRefinedBy, RISCV.Reg.toInt, Data.RISCV.max,
        RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, LLVM.Int.toReg] at hplain ⊢
      all_goals
        intros
        subst_vars
        try simp [hplain, RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, isRefinedBy]
      all_goals grind only [isRefinedBy]


theorem smin32_pattern_valid : Puddle.CTree.Pattern.Valid smin32_pattern := by
  unfold smin32_pattern lowerBinary
  provePuddleValid program sym =>
    rintro _ ty rfl hwidth
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x y p
    cases ty with | mk bw sign =>
      dsimp at hwidth
      subst bw
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.riscv_sextw]
      puddleStep sym [CanInterpretTo.riscv_sextw]
      puddleStep sym [CanInterpretTo.riscv_min]
      puddleStep sym [CanInterpretTo.cast_reg_int]
      have hplain := Data.RISCV.smin_refinement_32 (x := x) (y := y)
      cases x <;> cases y <;> simp [RuntimeValue.arrayIsRefinedBy_cons, Interp.isRefinedBy,
        RuntimeValue.isRefinedBy]
      all_goals simp [Id.run, pure, Pure.pure, Data.LLVM.Int.smin, isRefinedBy, RISCV.Reg.toInt, Data.RISCV.min,
        RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, LLVM.Int.toReg] at hplain ⊢
      all_goals
        intros
        subst_vars
        try simp [hplain, RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, isRefinedBy]
      all_goals grind only [isRefinedBy]


theorem and_pattern_valid : Puddle.CTree.Pattern.Valid and_pattern := by
  unfold and_pattern lowerBinary
  provePuddleValid program sym =>
    rintro _ ty rfl hwidth
    cases ty with | mk bw sign =>
      dsimp at hwidth
      rcases hwidth with h | h | h | h <;> subst bw
      all_goals
        simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
        intro x y p
        puddleStep sym [CanInterpretTo.cast_int_val']
        puddleStep sym [CanInterpretTo.cast_int_val']
        puddleStep sym [CanInterpretTo.riscv_and]
        puddleStep sym [CanInterpretTo.cast_reg_int]
        first
        | have hplain := Data.RISCV.and_refinement (x := x) (y := y)
        | have hplain := Data.RISCV.and_refinement_32 (x := x) (y := y)
        | have hplain := Data.RISCV.and_refinement_8 (x := x) (y := y)
        | have hplain := Data.RISCV.and_refinement_1 (x := x) (y := y)
        cases x <;> cases y <;> simp [RuntimeValue.arrayIsRefinedBy_cons, Interp.isRefinedBy,
        RuntimeValue.isRefinedBy]
        all_goals simp [Id.run, pure, Pure.pure, Data.LLVM.Int.and, isRefinedBy, RISCV.Reg.toInt, Data.RISCV.and,
        RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, LLVM.Int.toReg] at hplain ⊢
        all_goals
        intros
        subst_vars
        try simp [hplain, RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, isRefinedBy]
      all_goals grind only [isRefinedBy]


theorem or_pattern_valid : Puddle.CTree.Pattern.Valid or_pattern := by
  unfold or_pattern lowerBinary
  provePuddleValid program sym =>
    rintro _ ty rfl hwidth
    cases ty with | mk bw sign =>
      dsimp at hwidth
      rcases hwidth with h | h | h | h <;> subst bw
      all_goals
        simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
        intro x y p
        puddleStep sym [CanInterpretTo.cast_int_val']
        puddleStep sym [CanInterpretTo.cast_int_val']
        puddleStep sym [CanInterpretTo.riscv_or]
        puddleStep sym [CanInterpretTo.cast_reg_int]
        first
        | have hplain := Data.RISCV.or_refinement (x := x) (y := y)
        | have hplain := Data.RISCV.or_refinement_32 (x := x) (y := y)
        | have hplain := Data.RISCV.or_refinement_8 (x := x) (y := y)
        | have hplain := Data.RISCV.or_refinement_1 (x := x) (y := y)
        cases x <;> cases y <;> simp [RuntimeValue.arrayIsRefinedBy_cons, Interp.isRefinedBy,
        RuntimeValue.isRefinedBy]
        all_goals simp [Id.run, pure, Pure.pure, Data.LLVM.Int.or, isRefinedBy, RISCV.Reg.toInt, Data.RISCV.or,
        RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, LLVM.Int.toReg] at hplain ⊢
        all_goals
        intros
        subst_vars
        try simp [hplain, RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, isRefinedBy]
      all_goals grind only [isRefinedBy]


theorem umax_pattern_valid : Puddle.CTree.Pattern.Valid umax_pattern := by
  unfold umax_pattern lowerBinary
  provePuddleValid program sym =>
    rintro _ ty rfl hwidth
    cases ty with | mk bw sign =>
      dsimp at hwidth
      rcases hwidth with h | h <;> subst bw
      all_goals
        simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
        intro x y p
        puddleStep sym [CanInterpretTo.cast_int_val']
        puddleStep sym [CanInterpretTo.cast_int_val']
        puddleStep sym [CanInterpretTo.riscv_maxu]
        puddleStep sym [CanInterpretTo.cast_reg_int]
        first
        | have hplain := Data.RISCV.umax_refinement (x := x) (y := y)
        | have hplain := Data.RISCV.umax_refinement_32 (x := x) (y := y)
        cases x <;> cases y <;> simp [RuntimeValue.arrayIsRefinedBy_cons, Interp.isRefinedBy,
        RuntimeValue.isRefinedBy]
        all_goals simp [Id.run, pure, Pure.pure, Data.LLVM.Int.umax, isRefinedBy, RISCV.Reg.toInt, Data.RISCV.maxu,
        RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, LLVM.Int.toReg] at hplain ⊢
        all_goals
        intros
        subst_vars
        try simp [hplain, RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, isRefinedBy]
      all_goals grind only [isRefinedBy]


theorem umin_pattern_valid : Puddle.CTree.Pattern.Valid umin_pattern := by
  unfold umin_pattern lowerBinary
  provePuddleValid program sym =>
    rintro _ ty rfl hwidth
    cases ty with | mk bw sign =>
      dsimp at hwidth
      rcases hwidth with h | h <;> subst bw
      all_goals
        simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
        intro x y p
        puddleStep sym [CanInterpretTo.cast_int_val']
        puddleStep sym [CanInterpretTo.cast_int_val']
        puddleStep sym [CanInterpretTo.riscv_minu]
        puddleStep sym [CanInterpretTo.cast_reg_int]
        first
        | have hplain := Data.RISCV.umin_refinement (x := x) (y := y)
        | have hplain := Data.RISCV.umin_refinement_32 (x := x) (y := y)
        cases x <;> cases y <;> simp [RuntimeValue.arrayIsRefinedBy_cons, Interp.isRefinedBy,
        RuntimeValue.isRefinedBy]
        all_goals simp [Id.run, pure, Pure.pure, Data.LLVM.Int.umin, isRefinedBy, RISCV.Reg.toInt, Data.RISCV.minu,
        RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, LLVM.Int.toReg] at hplain ⊢
        all_goals
        intros
        subst_vars
        try simp [hplain, RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, isRefinedBy]
      all_goals grind only [isRefinedBy]


theorem fshl64_pattern_valid : Puddle.CTree.Pattern.Valid fshl64_pattern := by
  unfold fshl64_pattern lowerRotate
  provePuddleValid program sym =>
    rintro _ ty rfl hwidth
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x y p
    cases ty with | mk bw sign =>
      dsimp at hwidth
      subst bw
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.riscv_rol]
      puddleStep sym [CanInterpretTo.cast_reg_int]
      have hplain := Data.RISCV.fshl_rol_refinement (a := x) (c := y)
      cases x <;> cases y <;> simp [RuntimeValue.arrayIsRefinedBy_cons, Interp.isRefinedBy,
        RuntimeValue.isRefinedBy]
      all_goals simp [Id.run, pure, Pure.pure, Data.LLVM.Int.fshl, isRefinedBy, RISCV.Reg.toInt, Data.RISCV.rol,
        RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, LLVM.Int.toReg] at hplain ⊢
      all_goals
        intros
        subst_vars
        try simp [hplain, RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, isRefinedBy]
      all_goals grind only [isRefinedBy]


theorem fshl32_pattern_valid : Puddle.CTree.Pattern.Valid fshl32_pattern := by
  unfold fshl32_pattern lowerRotate
  provePuddleValid program sym =>
    rintro _ ty rfl hwidth
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x y p
    cases ty with | mk bw sign =>
      dsimp at hwidth
      subst bw
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.riscv_rolw]
      puddleStep sym [CanInterpretTo.cast_reg_int]
      have hplain := Data.RISCV.fshl_rol_refinement_32 (a := x) (c := y)
      cases x <;> cases y <;> simp [RuntimeValue.arrayIsRefinedBy_cons, Interp.isRefinedBy,
        RuntimeValue.isRefinedBy]
      all_goals simp [Id.run, pure, Pure.pure, Data.LLVM.Int.fshl, isRefinedBy, RISCV.Reg.toInt, Data.RISCV.rolw,
        RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, LLVM.Int.toReg] at hplain ⊢
      all_goals
        intros
        subst_vars
        try simp [hplain, RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, isRefinedBy]
      all_goals grind only [isRefinedBy]


theorem fshr64_pattern_valid : Puddle.CTree.Pattern.Valid fshr64_pattern := by
  unfold fshr64_pattern lowerRotate
  provePuddleValid program sym =>
    rintro _ ty rfl hwidth
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x y p
    cases ty with | mk bw sign =>
      dsimp at hwidth
      subst bw
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.riscv_ror]
      puddleStep sym [CanInterpretTo.cast_reg_int]
      have hplain := Data.RISCV.fshr_ror_refinement (a := x) (c := y)
      cases x <;> cases y <;> simp [RuntimeValue.arrayIsRefinedBy_cons, Interp.isRefinedBy,
        RuntimeValue.isRefinedBy]
      all_goals simp [Id.run, pure, Pure.pure, Data.LLVM.Int.fshr, isRefinedBy, RISCV.Reg.toInt, Data.RISCV.ror,
        RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, LLVM.Int.toReg] at hplain ⊢
      all_goals
        intros
        subst_vars
        try simp [hplain, RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, isRefinedBy]
      all_goals grind only [isRefinedBy]


theorem fshr32_pattern_valid : Puddle.CTree.Pattern.Valid fshr32_pattern := by
  unfold fshr32_pattern lowerRotate
  provePuddleValid program sym =>
    rintro _ ty rfl hwidth
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x y p
    cases ty with | mk bw sign =>
      dsimp at hwidth
      subst bw
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.riscv_rorw]
      puddleStep sym [CanInterpretTo.cast_reg_int]
      have hplain := Data.RISCV.fshr_ror_refinement_32 (a := x) (c := y)
      cases x <;> cases y <;> simp [RuntimeValue.arrayIsRefinedBy_cons, Interp.isRefinedBy,
        RuntimeValue.isRefinedBy]
      all_goals simp [Id.run, pure, Pure.pure, Data.LLVM.Int.fshr, isRefinedBy, RISCV.Reg.toInt, Data.RISCV.rorw,
        RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, LLVM.Int.toReg] at hplain ⊢
      all_goals
        intros
        subst_vars
        try simp [hplain, RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, isRefinedBy]
      all_goals grind only [isRefinedBy]


theorem sdiv64_pattern_valid : Puddle.CTree.Pattern.Valid sdiv64_pattern := by
  unfold sdiv64_pattern lowerBinary
  provePuddleValid program sym =>
    rintro _ ty rfl hwidth
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x y p
    cases ty with | mk bw sign =>
      dsimp at hwidth
      subst bw
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.riscv_div]
      puddleStep sym [CanInterpretTo.cast_reg_int]
      have hplain := Data.RISCV.sdiv_refinement (x := x) (y := y)
      have hsource := CanInterpretTo.llvm_sdiv_source 64 { bitwidth := 64, signedness := sign } p x y
      cases x <;> cases y <;> simp [RuntimeValue.arrayIsRefinedBy_cons, Interp.isRefinedBy,
        RuntimeValue.isRefinedBy]
      all_goals
        intros
        subst_vars
        apply CanInterpretTo.refines_int_result hsource
      all_goals simp [Id.run, pure, Pure.pure, Data.LLVM.Int.sdiv, isRefinedBy, RISCV.Reg.toInt, Data.RISCV.div,
        RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, LLVM.Int.toReg] at hplain ⊢
      all_goals
        intros
        subst_vars
        try simp [hplain, RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, isRefinedBy]
      all_goals grind only [isRefinedBy]


theorem sdiv32_pattern_valid : Puddle.CTree.Pattern.Valid sdiv32_pattern := by
  unfold sdiv32_pattern lowerBinary
  provePuddleValid program sym =>
    rintro _ ty rfl hwidth
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x y p
    cases ty with | mk bw sign =>
      dsimp at hwidth
      subst bw
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.riscv_divw]
      puddleStep sym [CanInterpretTo.cast_reg_int]
      have hplain := Data.RISCV.sdiv_refinement_32 (x := x) (y := y)
      have hsource := CanInterpretTo.llvm_sdiv_source 32 { bitwidth := 32, signedness := sign } p x y
      cases x <;> cases y <;> simp [RuntimeValue.arrayIsRefinedBy_cons, Interp.isRefinedBy,
        RuntimeValue.isRefinedBy]
      all_goals
        intros
        subst_vars
        apply CanInterpretTo.refines_int_result hsource
      all_goals simp [Id.run, pure, Pure.pure, Data.LLVM.Int.sdiv, isRefinedBy, RISCV.Reg.toInt, Data.RISCV.divw,
        RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, LLVM.Int.toReg] at hplain ⊢
      all_goals
        intros
        subst_vars
        try simp [hplain, RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, isRefinedBy]
      all_goals grind only [isRefinedBy]


theorem udiv64_pattern_valid : Puddle.CTree.Pattern.Valid udiv64_pattern := by
  unfold udiv64_pattern lowerBinary
  provePuddleValid program sym =>
    rintro _ ty rfl hwidth
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x y p
    cases ty with | mk bw sign =>
      dsimp at hwidth
      subst bw
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.riscv_divu]
      puddleStep sym [CanInterpretTo.cast_reg_int]
      have hplain := Data.RISCV.udiv_refinement (x := x) (y := y)
      have hsource := CanInterpretTo.llvm_udiv_source 64 { bitwidth := 64, signedness := sign } p x y
      cases x <;> cases y <;> simp [RuntimeValue.arrayIsRefinedBy_cons, Interp.isRefinedBy,
        RuntimeValue.isRefinedBy]
      all_goals
        intros
        subst_vars
        apply CanInterpretTo.refines_int_result hsource
      all_goals simp [Id.run, pure, Pure.pure, Data.LLVM.Int.udiv, isRefinedBy, RISCV.Reg.toInt, Data.RISCV.divu,
        RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, LLVM.Int.toReg] at hplain ⊢
      all_goals
        intros
        subst_vars
        try simp [hplain, RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, isRefinedBy]
      all_goals grind only [isRefinedBy]


theorem udiv32_pattern_valid : Puddle.CTree.Pattern.Valid udiv32_pattern := by
  unfold udiv32_pattern lowerBinary
  provePuddleValid program sym =>
    rintro _ ty rfl hwidth
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x y p
    cases ty with | mk bw sign =>
      dsimp at hwidth
      subst bw
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.riscv_divuw]
      puddleStep sym [CanInterpretTo.cast_reg_int]
      have hplain := Data.RISCV.udiv_refinement_32 (x := x) (y := y)
      have hsource := CanInterpretTo.llvm_udiv_source 32 { bitwidth := 32, signedness := sign } p x y
      cases x <;> cases y <;> simp [RuntimeValue.arrayIsRefinedBy_cons, Interp.isRefinedBy,
        RuntimeValue.isRefinedBy]
      all_goals
        intros
        subst_vars
        apply CanInterpretTo.refines_int_result hsource
      all_goals simp [Id.run, pure, Pure.pure, Data.LLVM.Int.udiv, isRefinedBy, RISCV.Reg.toInt, Data.RISCV.divuw,
        RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, LLVM.Int.toReg] at hplain ⊢
      all_goals
        intros
        subst_vars
        try simp [hplain, RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, isRefinedBy]
      all_goals grind only [isRefinedBy]


theorem srem64_pattern_valid : Puddle.CTree.Pattern.Valid srem64_pattern := by
  unfold srem64_pattern lowerBinary
  provePuddleValid program sym =>
    rintro _ ty rfl hwidth
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x y p
    cases ty with | mk bw sign =>
      dsimp at hwidth
      subst bw
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.riscv_rem]
      puddleStep sym [CanInterpretTo.cast_reg_int]
      have hplain := Data.RISCV.srem_refinement (x := x) (y := y)
      have hsource := CanInterpretTo.llvm_srem_source 64 { bitwidth := 64, signedness := sign } p x y
      cases x <;> cases y <;> simp [RuntimeValue.arrayIsRefinedBy_cons, Interp.isRefinedBy,
        RuntimeValue.isRefinedBy]
      all_goals
        intros
        subst_vars
        apply CanInterpretTo.refines_int_result hsource
      all_goals simp [Id.run, pure, Pure.pure, Data.LLVM.Int.srem, isRefinedBy, RISCV.Reg.toInt, Data.RISCV.rem,
        RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, LLVM.Int.toReg] at hplain ⊢
      all_goals
        intros
        subst_vars
        try simp [hplain, RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, isRefinedBy]
      all_goals grind only [isRefinedBy]


theorem srem32_pattern_valid : Puddle.CTree.Pattern.Valid srem32_pattern := by
  unfold srem32_pattern lowerBinary
  provePuddleValid program sym =>
    rintro _ ty rfl hwidth
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x y p
    cases ty with | mk bw sign =>
      dsimp at hwidth
      subst bw
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.riscv_remw]
      puddleStep sym [CanInterpretTo.cast_reg_int]
      have hplain := Data.RISCV.srem_refinement_32 (x := x) (y := y)
      have hsource := CanInterpretTo.llvm_srem_source 32 { bitwidth := 32, signedness := sign } p x y
      cases x <;> cases y <;> simp [RuntimeValue.arrayIsRefinedBy_cons, Interp.isRefinedBy,
        RuntimeValue.isRefinedBy]
      all_goals
        intros
        subst_vars
        apply CanInterpretTo.refines_int_result hsource
      all_goals simp [Id.run, pure, Pure.pure, Data.LLVM.Int.srem, isRefinedBy, RISCV.Reg.toInt, Data.RISCV.remw,
        RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, LLVM.Int.toReg] at hplain ⊢
      all_goals
        intros
        subst_vars
        try simp [hplain, RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, isRefinedBy]
      all_goals grind only [isRefinedBy]


theorem urem64_pattern_valid : Puddle.CTree.Pattern.Valid urem64_pattern := by
  unfold urem64_pattern lowerBinary
  provePuddleValid program sym =>
    rintro _ ty rfl hwidth
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x y p
    cases ty with | mk bw sign =>
      dsimp at hwidth
      subst bw
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.riscv_remu]
      puddleStep sym [CanInterpretTo.cast_reg_int]
      have hplain := Data.RISCV.urem_refinement (x := x) (y := y)
      have hsource := CanInterpretTo.llvm_urem_source 64 { bitwidth := 64, signedness := sign } p x y
      cases x <;> cases y <;> simp [RuntimeValue.arrayIsRefinedBy_cons, Interp.isRefinedBy,
        RuntimeValue.isRefinedBy]
      all_goals
        intros
        subst_vars
        apply CanInterpretTo.refines_int_result hsource
      all_goals simp [Id.run, pure, Pure.pure, Data.LLVM.Int.urem, isRefinedBy, RISCV.Reg.toInt, Data.RISCV.remu,
        RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, LLVM.Int.toReg] at hplain ⊢
      all_goals
        intros
        subst_vars
        try simp [hplain, RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, isRefinedBy]
      all_goals grind only [isRefinedBy]


theorem urem32_pattern_valid : Puddle.CTree.Pattern.Valid urem32_pattern := by
  unfold urem32_pattern lowerBinary
  provePuddleValid program sym =>
    rintro _ ty rfl hwidth
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x y p
    cases ty with | mk bw sign =>
      dsimp at hwidth
      subst bw
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.cast_int_val']
      puddleStep sym [CanInterpretTo.riscv_remuw]
      puddleStep sym [CanInterpretTo.cast_reg_int]
      have hplain := Data.RISCV.urem_refinement_32 (x := x) (y := y)
      have hsource := CanInterpretTo.llvm_urem_source 32 { bitwidth := 32, signedness := sign } p x y
      cases x <;> cases y <;> simp [RuntimeValue.arrayIsRefinedBy_cons, Interp.isRefinedBy,
        RuntimeValue.isRefinedBy]
      all_goals
        intros
        subst_vars
        apply CanInterpretTo.refines_int_result hsource
      all_goals simp [Id.run, pure, Pure.pure, Data.LLVM.Int.urem, isRefinedBy, RISCV.Reg.toInt, Data.RISCV.remuw,
        RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, LLVM.Int.toReg] at hplain ⊢
      all_goals
        intros
        subst_vars
        try simp [hplain, RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, isRefinedBy]
      all_goals grind only [isRefinedBy]


namespace Puddle.CTree
@[simp] theorem CanInterpretTo.llvm_sext (w : Nat) (ty : IntegerType)
    (h : w < ty.bitwidth) (p : propertiesOf (OpCode.llvm .sext)) (x : Data.LLVM.Int w)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .sext) p #[TypeAttr.of IntegerType ty] #[.int w x] r ↔
      r = .ok #[.int ty.bitwidth (Data.LLVM.Int.sext x ty.bitwidth h)] := by
  unfold CanInterpretTo
  change (∀ memory, PureOrErr.CanInterpretTo
    (if h' : ty.bitwidth ≤ w then fail else
      pure (#[.int ty.bitwidth (Data.LLVM.Int.sext x ty.bitwidth (Nat.lt_of_not_ge h'))], memory, none))
    (r.map (·, memory, none))) ↔ _
  cases r <;> simp [Nat.not_le.mpr h]
end Puddle.CTree

private theorem sextb_refinement_generic (w : Nat) (h : 8 < w) (hw : w ≤ 64)
    (x : Data.LLVM.Int 8) :
    Data.LLVM.Int.sext x w h ⊒ RISCV.Reg.toInt (Data.RISCV.sextb (LLVM.Int.toReg x)) w := by
  cases x <;> simp [Data.LLVM.Int.sext, isRefinedBy, Id.run, RISCV.Reg.toInt,
    Data.RISCV.sextb, LLVM.Int.toReg]
  change BitVec.signExtend w _ = BitVec.setWidth w (BitVec.signExtend 64 (BitVec.extractLsb' 0 8 _))
  rw [BitVec.extractLsb'_eq_self]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_signExtend, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb']
  have hi64 : i < 64 := by omega
  simp [hi, hi64]
private theorem sexth_refinement_generic (w : Nat) (h : 16 < w) (hw : w ≤ 64)
    (x : Data.LLVM.Int 16) :
    Data.LLVM.Int.sext x w h ⊒ RISCV.Reg.toInt (Data.RISCV.sexth (LLVM.Int.toReg x)) w := by
  cases x <;> simp [Data.LLVM.Int.sext, isRefinedBy, Id.run, RISCV.Reg.toInt,
    Data.RISCV.sexth, LLVM.Int.toReg]
  change BitVec.signExtend w _ = BitVec.setWidth w (BitVec.signExtend 64 (BitVec.extractLsb' 0 16 _))
  rw [BitVec.extractLsb'_eq_self]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_signExtend, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb']
  have hi64 : i < 64 := by omega
  simp [hi, hi64]

private theorem sextw_refinement_generic (w : Nat) (h : 32 < w) (hw : w ≤ 64)
    (x : Data.LLVM.Int 32) :
    Data.LLVM.Int.sext x w h ⊒ RISCV.Reg.toInt (Data.RISCV.sextw (LLVM.Int.toReg x)) w := by
  cases x with
  | poison => simp [Data.LLVM.Int.sext, isRefinedBy, Id.run]
  | val a =>
    have heq := Data.RISCV.sext_refinement_32_64 (h := by decide) (x := .val a)
    simp [Data.LLVM.Int.sext, isRefinedBy, Id.run, RISCV.Reg.toInt] at heq
    simp only [Data.LLVM.Int.sext, Id.run, isRefinedBy, RISCV.Reg.toInt]
    rw [← heq]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_signExtend, BitVec.getLsbD_setWidth]
    have hi64 : i < 64 := by omega
    simp [hi, hi64]

namespace Puddle.CTree
@[simp] theorem CanInterpretTo.llvm_zext (w : Nat) (ty : IntegerType)
    (h : w < ty.bitwidth) (p : propertiesOf (OpCode.llvm .zext)) (x : Data.LLVM.Int w)
    (r : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .zext) p #[TypeAttr.of IntegerType ty] #[.int w x] r ↔
      r = .ok #[.int ty.bitwidth (Data.LLVM.Int.zext x ty.bitwidth p.nneg h)] := by
  unfold CanInterpretTo
  change (∀ memory, PureOrErr.CanInterpretTo
    (if h' : ty.bitwidth ≤ w then fail else
      pure (#[.int ty.bitwidth (Data.LLVM.Int.zext x ty.bitwidth p.nneg (Nat.lt_of_not_ge h'))], memory, none))
    (r.map (·, memory, none))) ↔ _
  cases r <;> simp [Nat.not_le.mpr h]
end Puddle.CTree



private theorem zextb_refinement_generic (w : Nat) (h : 8 < w) (hw : w ≤ 64)
    (nneg : Bool) (x : Data.LLVM.Int 8) :
    Data.LLVM.Int.zext x w nneg h ⊒ RISCV.Reg.toInt (Data.RISCV.zextb (LLVM.Int.toReg x)) w := by
  cases x with
  | poison => simp [Data.LLVM.Int.zext, isRefinedBy, Id.run]
  | val a =>
    have heq := Data.RISCV.zext_refinement_8_64 (h := by decide) (b := false) (x := .val a)
    simp [Data.LLVM.Int.zext, isRefinedBy, Id.run, pure, Pure.pure, RISCV.Reg.toInt] at heq
    by_cases hn : nneg ∧ a.msb
    · simp [Data.LLVM.Int.zext, isRefinedBy, Id.run, pure, Pure.pure, hn]
    · simp [Data.LLVM.Int.zext, isRefinedBy, Id.run, pure, Pure.pure, hn, RISCV.Reg.toInt]
      rw [← heq]
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_setWidth]
      have hi64 : i < 64 := by omega
      simp [hi, hi64]

private theorem zexth_refinement_generic (w : Nat) (h : 16 < w) (hw : w ≤ 64)
    (nneg : Bool) (x : Data.LLVM.Int 16) :
    Data.LLVM.Int.zext x w nneg h ⊒ RISCV.Reg.toInt (Data.RISCV.zexth (LLVM.Int.toReg x)) w := by
  cases x with
  | poison => simp [Data.LLVM.Int.zext, isRefinedBy, Id.run]
  | val a =>
    have heq := Data.RISCV.zext_refinement_16_64 (h := by decide) (b := false) (x := .val a)
    simp [Data.LLVM.Int.zext, isRefinedBy, Id.run, pure, Pure.pure, RISCV.Reg.toInt] at heq
    by_cases hn : nneg ∧ a.msb
    · simp [Data.LLVM.Int.zext, isRefinedBy, Id.run, pure, Pure.pure, hn]
    · simp [Data.LLVM.Int.zext, isRefinedBy, Id.run, pure, Pure.pure, hn, RISCV.Reg.toInt]
      rw [← heq]
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_setWidth]
      have hi64 : i < 64 := by omega
      simp [hi, hi64]

private theorem zextw_refinement_generic (w : Nat) (h : 32 < w) (hw : w ≤ 64)
    (nneg : Bool) (x : Data.LLVM.Int 32) :
    Data.LLVM.Int.zext x w nneg h ⊒ RISCV.Reg.toInt (Data.RISCV.zextw (LLVM.Int.toReg x)) w := by
  cases x with
  | poison => simp [Data.LLVM.Int.zext, isRefinedBy, Id.run]
  | val a =>
    have heq := Data.RISCV.zext_refinement_32_64 (h := by decide) (b := false) (x := .val a)
    simp [Data.LLVM.Int.zext, isRefinedBy, Id.run, pure, Pure.pure, RISCV.Reg.toInt] at heq
    by_cases hn : nneg ∧ a.msb
    · simp [Data.LLVM.Int.zext, isRefinedBy, Id.run, pure, Pure.pure, hn]
    · simp [Data.LLVM.Int.zext, isRefinedBy, Id.run, pure, Pure.pure, hn, RISCV.Reg.toInt]
      rw [← heq]
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_setWidth]
      have hi64 : i < 64 := by omega
      simp [hi, hi64]

theorem sext8_pattern_valid : Puddle.CTree.Pattern.Valid sext8_pattern := by
  unfold sext8_pattern lowerExt
  provePuddleValid program sym =>
    rintro _ opType rfl hop
    rintro _ resType rfl hlo hhi
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x p
    cases opType with | mk obw sign =>
      dsimp at hop
      subst obw
      cases resType with | mk resw sign2 =>
        dsimp at hlo hhi
        puddleStep sym [CanInterpretTo.cast_int_val']
        puddleStep sym [CanInterpretTo.riscv_sextb]
        puddleStep sym [CanInterpretTo.cast_reg_int]
        have hplain := sextb_refinement_generic resw hlo hhi x
        cases x <;> simp [hlo, RuntimeValue.arrayIsRefinedBy_cons, Interp.isRefinedBy,
          RuntimeValue.isRefinedBy]
        all_goals
          intros
          subst_vars
          try simp [RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy,
            Interp.isRefinedBy, isRefinedBy, LLVM.Int.toReg, Data.LLVM.Int.sext,
            Data.LLVM.Int.zext, Id.run, pure, Pure.pure] at hplain ⊢
        all_goals grind only [isRefinedBy]

theorem sext16_pattern_valid : Puddle.CTree.Pattern.Valid sext16_pattern := by
  unfold sext16_pattern lowerExt
  provePuddleValid program sym =>
    rintro _ opType rfl hop
    rintro _ resType rfl hlo hhi
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x p
    cases opType with | mk obw sign =>
      dsimp at hop
      subst obw
      cases resType with | mk resw sign2 =>
        dsimp at hlo hhi
        puddleStep sym [CanInterpretTo.cast_int_val']
        puddleStep sym [CanInterpretTo.riscv_sexth]
        puddleStep sym [CanInterpretTo.cast_reg_int]
        have hplain := sexth_refinement_generic resw hlo hhi x
        cases x <;> simp [hlo, RuntimeValue.arrayIsRefinedBy_cons, Interp.isRefinedBy,
          RuntimeValue.isRefinedBy]
        all_goals
          intros
          subst_vars
          try simp [RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy,
            Interp.isRefinedBy, isRefinedBy, LLVM.Int.toReg, Data.LLVM.Int.sext,
            Data.LLVM.Int.zext, Id.run, pure, Pure.pure] at hplain ⊢
        all_goals grind only [isRefinedBy]

theorem sext32_pattern_valid : Puddle.CTree.Pattern.Valid sext32_pattern := by
  unfold sext32_pattern lowerExt
  provePuddleValid program sym =>
    rintro _ opType rfl hop
    rintro _ resType rfl hlo hhi
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x p
    cases opType with | mk obw sign =>
      dsimp at hop
      subst obw
      cases resType with | mk resw sign2 =>
        dsimp at hlo hhi
        puddleStep sym [CanInterpretTo.cast_int_val']
        puddleStep sym [CanInterpretTo.riscv_sextw]
        puddleStep sym [CanInterpretTo.cast_reg_int]
        have hplain := sextw_refinement_generic resw hlo hhi x
        cases x <;> simp [hlo, RuntimeValue.arrayIsRefinedBy_cons, Interp.isRefinedBy,
          RuntimeValue.isRefinedBy]
        all_goals
          intros
          subst_vars
          try simp [RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy,
            Interp.isRefinedBy, isRefinedBy, LLVM.Int.toReg, Data.LLVM.Int.sext,
            Data.LLVM.Int.zext, Id.run, pure, Pure.pure] at hplain ⊢
        all_goals grind only [isRefinedBy]

theorem zext8_pattern_valid : Puddle.CTree.Pattern.Valid zext8_pattern := by
  unfold zext8_pattern lowerExt
  provePuddleValid program sym =>
    rintro _ opType rfl hop
    rintro _ resType rfl hlo hhi
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x p
    cases opType with | mk obw sign =>
      dsimp at hop
      subst obw
      cases resType with | mk resw sign2 =>
        dsimp at hlo hhi
        puddleStep sym [CanInterpretTo.cast_int_val']
        puddleStep sym [CanInterpretTo.riscv_zextb]
        puddleStep sym [CanInterpretTo.cast_reg_int]
        have hplain := zextb_refinement_generic resw hlo hhi p.nneg x
        cases x <;> simp [hlo, RuntimeValue.arrayIsRefinedBy_cons, Interp.isRefinedBy,
          RuntimeValue.isRefinedBy]
        all_goals
          intros
          subst_vars
          try simp [RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy,
            Interp.isRefinedBy, isRefinedBy, LLVM.Int.toReg, Data.LLVM.Int.sext,
            Data.LLVM.Int.zext, Id.run, pure, Pure.pure] at hplain ⊢
        all_goals grind only [isRefinedBy]

theorem zext16_pattern_valid : Puddle.CTree.Pattern.Valid zext16_pattern := by
  unfold zext16_pattern lowerExt
  provePuddleValid program sym =>
    rintro _ opType rfl hop
    rintro _ resType rfl hlo hhi
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x p
    cases opType with | mk obw sign =>
      dsimp at hop
      subst obw
      cases resType with | mk resw sign2 =>
        dsimp at hlo hhi
        puddleStep sym [CanInterpretTo.cast_int_val']
        puddleStep sym [CanInterpretTo.riscv_zexth]
        puddleStep sym [CanInterpretTo.cast_reg_int]
        have hplain := zexth_refinement_generic resw hlo hhi p.nneg x
        cases x <;> simp [hlo, RuntimeValue.arrayIsRefinedBy_cons, Interp.isRefinedBy,
          RuntimeValue.isRefinedBy]
        all_goals
          intros
          subst_vars
          try simp [RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy,
            Interp.isRefinedBy, isRefinedBy, LLVM.Int.toReg, Data.LLVM.Int.sext,
            Data.LLVM.Int.zext, Id.run, pure, Pure.pure] at hplain ⊢
        all_goals grind only [isRefinedBy]

theorem zext32_pattern_valid : Puddle.CTree.Pattern.Valid zext32_pattern := by
  unfold zext32_pattern lowerExt
  provePuddleValid program sym =>
    rintro _ opType rfl hop
    rintro _ resType rfl hlo hhi
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x p
    cases opType with | mk obw sign =>
      dsimp at hop
      subst obw
      cases resType with | mk resw sign2 =>
        dsimp at hlo hhi
        puddleStep sym [CanInterpretTo.cast_int_val']
        puddleStep sym [CanInterpretTo.riscv_zextw]
        puddleStep sym [CanInterpretTo.cast_reg_int]
        have hplain := zextw_refinement_generic resw hlo hhi p.nneg x
        cases x <;> simp [hlo, RuntimeValue.arrayIsRefinedBy_cons, Interp.isRefinedBy,
          RuntimeValue.isRefinedBy]
        all_goals
          intros
          subst_vars
          try simp [RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy,
            Interp.isRefinedBy, isRefinedBy, LLVM.Int.toReg, Data.LLVM.Int.sext,
            Data.LLVM.Int.zext, Id.run, pure, Pure.pure] at hplain ⊢
        all_goals grind only [isRefinedBy]

end Veir
