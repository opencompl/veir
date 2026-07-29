module

import Veir.Meta.OpCode
public import Veir.Dialects.Arith.OpInfo
public import Veir.Dialects.Builtin.OpInfo
public import Veir.Dialects.Func.OpInfo
public import Veir.Dialects.LLVM.OpInfo
public import Veir.Dialects.RISCV.OpInfo
public import Veir.Dialects.RISCV_Cf.OpInfo
public import Veir.Dialects.RISCV_Stack.OpInfo
public import Veir.Dialects.RV64.OpInfo
public import Veir.Dialects.ModArith.OpInfo
public import Veir.Dialects.Cf.OpInfo
public import Veir.Dialects.Comb.OpInfo
public import Veir.Dialects.HW.OpInfo
public import Veir.Dialects.Datapath.OpInfo
public import Veir.Dialects.Test.OpInfo

public import Veir.IR.Basic
public import Veir.OpCode

namespace Veir

public section

/--
  A type family that maps an operation code to the type of its properties.
  For operations that do not have any properties, the type is `Unit`.
-/
@[expose, properties_of]
def _propertiesOf (opCode : OpCode) : Type :=
match opCode with
| .arith op => Arith.propertiesOf op
| .llvm op => Llvm.propertiesOf op
| .riscv op => Riscv.propertiesOf op
| .riscv_cf op => Riscv_Cf.propertiesOf op
| .riscv_stack op => Riscv_Stack.propertiesOf op
| .rv64 op => Rv64.propertiesOf op
| .mod_arith op => Mod_Arith.propertiesOf op
| .cf op => Cf.propertiesOf op
| .comb op => Comb.propertiesOf op
| .hw op => HW.propertiesOf op
| .builtin op => Builtin.propertiesOf op
| .func op => Func.propertiesOf op
| .datapath op => Datapath.propertiesOf op
| .test op => Test.propertiesOf op

/--
  Does this OpCode count as an MLIR basic block terminator?
-/
def OpCode.isTerminator (opCode : OpCode) : Bool :=
  match opCode with
  | .cf .br | .cf .cond_br
  | .func .return
  | .llvm .br | .llvm .cond_br | .llvm .return | .llvm .unreachable
  | .riscv_cf .branch | .riscv_cf .beq | .riscv_cf .bne
  | .riscv_cf .beqz | .riscv_cf .bnez
  | .riscv_cf .blt | .riscv_cf .bge | .riscv_cf .bltu | .riscv_cf .bgeu
  | .hw .output => true
  | _ => false

/--
  Does an operation with this opcode read memory?
-/
def OpCode.readsMemory (opCode : OpCode) : Bool :=
  match opCode with
  | .arith op => Arith.readsMemory op
  | .llvm op => Llvm.readsMemory op
  | .riscv op => Riscv.readsMemory op
  | .riscv_cf op => Riscv_Cf.readsMemory op
  | .riscv_stack op => Riscv_Stack.readsMemory op
  | .rv64 op => Rv64.readsMemory op
  | .mod_arith op => Mod_Arith.readsMemory op
  | .cf op => Cf.readsMemory op
  | .comb op => Comb.readsMemory op
  | .hw op => HW.readsMemory op
  | .builtin op => Builtin.readsMemory op
  | .func op => Func.readsMemory op
  | .datapath op => Datapath.readsMemory op
  | .test op => Test.readsMemory op

/--
  Does an operation with this opcode and these properties have effects that
  make it ineligible for DCE and other transformations that add / remove /
  rearrange instructions?

  NOTE: ¬ hasSideEffects does not imply that an operation is safe to
        speculate. For that we also need it to never trigger immediate
        UB. We'll have to deal with this later on.

  Also see:
  https://mlir.llvm.org/docs/Rationale/SideEffectsAndSpeculation/
-/
def OpCode.hasSideEffects (opCode : OpCode) (props : _propertiesOf opCode) : Bool :=
  match opCode, props with
  | .arith op, props => Arith.hasSideEffects op props
  | .llvm op, props => Llvm.hasSideEffects op props
  | .riscv op, props => Riscv.hasSideEffects op props
  | .riscv_cf op, props => Riscv_Cf.hasSideEffects op props
  | .riscv_stack op, props => Riscv_Stack.hasSideEffects op props
  | .rv64 op, props => Rv64.hasSideEffects op props
  | .mod_arith op, props => Mod_Arith.hasSideEffects op props
  | .cf op, props => Cf.hasSideEffects op props
  | .comb op, props => Comb.hasSideEffects op props
  | .hw op, props => HW.hasSideEffects op props
  | .builtin op, props => Builtin.hasSideEffects op props
  | .func op, props => Func.hasSideEffects op props
  | .datapath op, props => Datapath.hasSideEffects op props
  | .test op, props => Test.hasSideEffects op props

inductive RegionKind where
| SSACFG
| Graph
deriving Inhabited, Repr, DecidableEq

/--
  Return the kind of the region with the given index inside this operation.
  This mirrors MLIR's RegionKindInterface default: regions are SSACFG unless
  the operation is known to define graph regions.
-/
def OpCode.getRegionKind (opCode : OpCode) (_index : Nat) : RegionKind :=
  match opCode with
  | .builtin .module
  | .builtin .unregistered
  | .test .test => .Graph
  | _ => .SSACFG

/--
  Whether definitions in the indexed region of this opcode must dominate
  their uses.
-/
def OpCode.hasSSADominance (opCode : OpCode) (index : Nat) : Bool :=
  match opCode with
  | .arith op => Arith.hasSSADominance op index
  | .llvm op => Llvm.hasSSADominance op index
  | .riscv op => Riscv.hasSSADominance op index
  | .riscv_cf op => Riscv_Cf.hasSSADominance op index
  | .riscv_stack op => Riscv_Stack.hasSSADominance op index
  | .rv64 op => Rv64.hasSSADominance op index
  | .mod_arith op => Mod_Arith.hasSSADominance op index
  | .cf op => Cf.hasSSADominance op index
  | .comb op => Comb.hasSSADominance op index
  | .hw op => HW.hasSSADominance op index
  | .builtin op => Builtin.hasSSADominance op index
  | .func op => Func.hasSSADominance op index
  | .datapath op => Datapath.hasSSADominance op index
  | .test op => Test.hasSSADominance op index

/--
  Does this `OpCode` materialize a literal constant value, i.e. an op
  whose single result is a compile-time constant taken from its
  properties, with no SSA operands and no side effects?

  This is the analogue of MLIR's `ConstantLike` op trait, which likewise
  covers `llvm.mlir.poison`: poison is a perfectly good constant.
-/
def OpCode.isConstantLike (opCode : OpCode) : Bool :=
  match opCode with
  | .arith op => Arith.isConstantLike op
  | .llvm op => Llvm.isConstantLike op
  | .riscv op => Riscv.isConstantLike op
  | .riscv_cf op => Riscv_Cf.isConstantLike op
  | .riscv_stack op => Riscv_Stack.isConstantLike op
  | .rv64 op => Rv64.isConstantLike op
  | .mod_arith op => Mod_Arith.isConstantLike op
  | .cf op => Cf.isConstantLike op
  | .comb op => Comb.isConstantLike op
  | .hw op => HW.isConstantLike op
  | .builtin op => Builtin.isConstantLike op
  | .func op => Func.isConstantLike op
  | .datapath op => Datapath.isConstantLike op
  | .test op => Test.isConstantLike op

def Properties.fromAttrDict (opCode : OpCode) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (_propertiesOf opCode) :=
  match opCode with
  | .arith op => Arith.fromAttrDict op attrDict
  | .llvm op => Llvm.fromAttrDict op attrDict
  | .riscv op => Riscv.fromAttrDict op attrDict
  | .riscv_cf op => Riscv_Cf.fromAttrDict op attrDict
  | .riscv_stack op => Riscv_Stack.fromAttrDict op attrDict
  | .rv64 op => Rv64.fromAttrDict op attrDict
  | .mod_arith op => Mod_Arith.fromAttrDict op attrDict
  | .cf op => Cf.fromAttrDict op attrDict
  | .comb op => Comb.fromAttrDict op attrDict
  | .hw op => HW.fromAttrDict op attrDict
  | .builtin op => Builtin.fromAttrDict op attrDict
  | .func op => Func.fromAttrDict op attrDict
  | .datapath op => Datapath.fromAttrDict op attrDict
  | .test op => Test.fromAttrDict op attrDict

/--
  Converts the properties of an operation into a dictionary of attributes.
-/
def Properties.toAttrDict
    (opCode : OpCode) (props : _propertiesOf opCode) :
    Std.HashMap ByteArray Attribute :=
  match opCode, props with
  | .arith op, props => Arith.toAttrDict op props
  | .llvm op, props => Llvm.toAttrDict op props
  | .riscv op, props => Riscv.toAttrDict op props
  | .riscv_cf op, props => Riscv_Cf.toAttrDict op props
  | .riscv_stack op, props => Riscv_Stack.toAttrDict op props
  | .rv64 op, props => Rv64.toAttrDict op props
  | .mod_arith op, props => Mod_Arith.toAttrDict op props
  | .cf op, props => Cf.toAttrDict op props
  | .comb op, props => Comb.toAttrDict op props
  | .hw op, props => HW.toAttrDict op props
  | .builtin op, props => Builtin.toAttrDict op props
  | .func op, props => Func.toAttrDict op props
  | .datapath op, props => Datapath.toAttrDict op props
  | .test op, props => Test.toAttrDict op props

instance : HasDialectOpInfo OpCode where
  propertiesOf := _propertiesOf
  fromAttrDict := Properties.fromAttrDict
  toAttrDict := Properties.toAttrDict
  hasSideEffects := OpCode.hasSideEffects
  readsMemory := OpCode.readsMemory
  isConstantLike := OpCode.isConstantLike
  hasSSADominance := OpCode.hasSSADominance

instance : HasOpInfo OpCode where

#generate_has_dialect_instances OpCode

abbrev propertiesOf := HasOpInfo.propertiesOf (self := instHasOpInfoOpCode)

/--
  Is this `OpCode` commutative in its operands, i.e. `op x y` always
  computes the same value as `op y x`?
-/
def OpCode.isCommutative (opCode : OpCode) : Bool :=
  match opCode with
  | .arith .addi | .arith .muli
  | .arith .andi | .arith .ori | .arith .xori
  | .arith .maxsi | .arith .maxui | .arith .minsi | .arith .minui
  | .arith .addui_extended
  | .arith .mulsi_extended | .arith .mului_extended
  | .llvm .add | .llvm .mul
  | .llvm .and | .llvm .or | .llvm .xor
  | .llvm .intr__smax | .llvm .intr__smin | .llvm .intr__umax | .llvm .intr__umin
  | .llvm .intr__sadd__sat | .llvm .intr__uadd__sat
  | .llvm .fadd | .llvm .fmul
  | .riscv .add | .riscv .and | .riscv .or | .riscv .xor | .riscv .xnor
  | .riscv .mul | .riscv .mulh | .riscv .mulhu
  | .riscv .max | .riscv .maxu | .riscv .min | .riscv .minu
  | .riscv .addw | .riscv .mulw => true
  | _ => false
