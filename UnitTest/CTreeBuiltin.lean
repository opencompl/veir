import Veir.Dialects.Builtin.Interpreter
import Veir.Interpreter.CTreeRefinement

open Veir Veir.Data

private abbrev builtinCast (type : TypeAttr) (value : RuntimeValue) (memory : MemoryState) :=
  Builtin.interpretOpCTree .unrealized_conversion_cast () #[type] #[value] #[] memory

private theorem choose_refines_return (choice : FreezeCIn) (result : FreezeC choice → α)
    (value : FreezeC choice) :
    Tree.Refines Eq
      (do let bits ← CTree.CTree.choose choice; pure (result bits))
      (pure (result value)) := by
  simp [Tree.Refines, CTree.CTree.choose_def, CTree.CTree.tau_def, Bind.bind]

/- A poison integer or pointer must permit the register produced by a concrete
   refining input, including a nonzero register. -/
example (bits : BitVec 64) :
    RuntimeValue.isRefinedBy (.int 64 .poison) (.int 64 (.val bits)) := by
  exact ⟨rfl, by simp⟩

example (pointer : Pointer) :
    RuntimeValue.isRefinedBy (.addr .poison) (.addr (.val pointer)) := by
  trivial

example (bits : BitVec 64) (memory : MemoryState) :
    Tree.Refines Eq
      (builtinCast RegisterType.mk (.int 64 .poison) memory)
      (builtinCast RegisterType.mk (.int 64 (.val bits)) memory) := by
  change Tree.Refines Eq
    (do let value ← CTree.CTree.choose (SubC := FreezeC) (FreezeCIn.mk 64)
        pure (#[RuntimeValue.reg ⟨value⟩], memory, none))
    (pure (#[RuntimeValue.reg ⟨bits⟩], memory, none))
  exact choose_refines_return (.mk 64) _ bits

/- Concretizing a narrow integer preserves the cast's zero extension. -/
example (bits : BitVec 8) (memory : MemoryState) :
    Tree.Refines Eq
      (builtinCast RegisterType.mk (.int 8 .poison) memory)
      (builtinCast RegisterType.mk (.int 8 (.val bits)) memory) := by
  change Tree.Refines Eq
    (do let value ← CTree.CTree.choose (SubC := FreezeC) (FreezeCIn.mk 8)
        pure (#[RuntimeValue.reg ⟨value.zeroExtend 64⟩], memory, none))
    (pure (#[RuntimeValue.reg ⟨bits.zeroExtend 64⟩], memory, none))
  exact choose_refines_return (.mk 8) _ bits

example (pointer : Pointer) (memory : MemoryState) :
    Tree.Refines Eq
      (builtinCast RegisterType.mk (.addr .poison) memory)
      (builtinCast RegisterType.mk (.addr (.val pointer)) memory) := by
  change Tree.Refines Eq
    (do let value ← CTree.CTree.choose (SubC := FreezeC) (FreezeCIn.mk 64)
        pure (#[RuntimeValue.reg ⟨value⟩], memory, none))
    (pure (#[RuntimeValue.reg ⟨pointer.address.toBitVec⟩], memory, none))
  exact choose_refines_return (.mk 64) _ pointer.address.toBitVec

private def partialByte : LLVM.Byte 8 := ⟨4, 1, by decide⟩

example : partialByte ⊒ LLVM.Byte.fromBitVec 5 := by
  unfold partialByte LLVM.Byte.isRefinedBy LLVM.Byte.fromBitVec
  decide

/- The unknown low bit may become one; retaining fixed zero here was unsound. -/
example (memory : MemoryState) :
    Tree.Refines Eq
      (builtinCast RegisterType.mk (.byte 8 partialByte) memory)
      (builtinCast RegisterType.mk (.byte 8 (.fromBitVec 5)) memory) := by
  change Tree.Refines Eq
    (do let bits ← CTree.CTree.choose (SubC := FreezeC) (FreezeCIn.mk 8)
        pure (#[RuntimeValue.reg ⟨(4#8 ||| (1#8 &&& bits)).zeroExtend 64⟩], memory, none))
    (pure (#[RuntimeValue.reg ⟨5⟩], memory, none))
  exact choose_refines_return (.mk 8) _ 1

example (memory : MemoryState) :
    Tree.Refines Eq
      (builtinCast (IntegerType.signless 8) (.byte 8 partialByte) memory)
      (builtinCast (IntegerType.signless 8) (.byte 8 (.fromBitVec 5)) memory) := by
  change Tree.Refines Eq
    (do let bits ← CTree.CTree.choose (SubC := FreezeC) (FreezeCIn.mk 8)
        pure (#[RuntimeValue.int 8 (.val (4#8 ||| (1#8 &&& bits)))], memory, none))
    (pure (#[RuntimeValue.int 8 (.val 5)], memory, none))
  exact choose_refines_return (.mk 8) _ 1

/- An entirely poisoned byte still carries poison across an integer cast. -/
example (memory : MemoryState) :
    builtinCast (IntegerType.signless 8) (.byte 8 .allPoison) memory =
      pure (#[RuntimeValue.int 8 .poison], memory, none) := by
  rfl
