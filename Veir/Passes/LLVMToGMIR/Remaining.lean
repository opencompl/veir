module

import all Veir.Passes.Legalization.Validity.Common
import all Veir.Dialects.GMIR.OpInfo
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.LLVM.Byte.Basic
import all Veir.Data.LLVM.Ptr.Basic
import all Veir.Data.Casting
import all Veir.Data.Refinement
import all Veir.Interpreter.Memory

/-!
# What remains to certify the last LLVM to gMIR translations

The local lemmas that would close the 11 unproven patterns of `llvm-to-gmir` (see `Unproven` in
`Veir.Passes.LLVMToGMIR.Validity`), with their proofs left as `sorry`. Most of these patterns are
wrong as matched, so each lemma takes as hypothesis the condition that the rule or its matcher
would have to check:

| Pattern | Lemma | Condition |
|---|---|---|
| `ctlz`, `cttz`, their zero-poison forms, `ctpop` | `resizeCount_self` | the result has the operand's width (typed match) |
| `icmp` | none: reflexivity | the result is `i1` (typed match) |
| byte `trunc` | `byte_trunc_frozen` | no `nsw`/`nuw` |
| byte `shl`, byte `lshr` | `byte_shl_frozen`, `byte_lshr_frozen` | the byte is not entirely poison |
| byte/integer `bitcast` | `byte_toInt_frozen` | a nonzero width |
| static `alloca` | `ptrFromInt_toInt` | the stack object has the size of the `alloca` |

The static `alloca` also needs its stack object's size to be the size of the `llvm.alloca`. The
pattern computes it from the IR (`MatchProg.inspectOperation`), which `Pattern.Valid` quantifies
over, so this needs the rule or the framework to tie it to the matched operation; it is not a
lemma.
-/

namespace Veir.LLVMToGMIR.CTreeProofs

open Data

/-- A count resized to the width it has is unchanged. -/
private theorem resizeCount_self {w : Nat} (c : LLVM.Int w) : resizeCount w c = c := by
  sorry

/-- `llvm.trunc` of a byte, through the integer of its bits, without the flags that LLVM ignores on
bytes. -/
private theorem byte_trunc_frozen {w w' : Nat} (h : w > w') (b : LLVM.Byte w) :
    LLVM.Byte.isRefinedBy (b.trunc w')
      (LLVM.Byte.fromInt ((_root_.LLVM.Byte.toFrozenInt b).trunc w' false false h)) := by
  sorry

/-- `llvm.shl` of a byte that is not entirely poison, through the integer of its bits. -/
private theorem byte_shl_frozen {w : Nat} (b : LLVM.Byte w) (y : LLVM.Int w) (nuw : Bool)
    (hb : b.poison ≠ BitVec.allOnes w) :
    LLVM.Byte.isRefinedBy (b.shl y nuw)
      (LLVM.Byte.fromInt ((_root_.LLVM.Byte.toFrozenInt b).shl (shiftAmount w y) false nuw)) := by
  sorry

/-- `llvm.lshr` of a byte that is not entirely poison, through the integer of its bits. -/
private theorem byte_lshr_frozen {w : Nat} (b : LLVM.Byte w) (y : LLVM.Int w) (exact : Bool)
    (hb : b.poison ≠ BitVec.allOnes w) :
    LLVM.Byte.isRefinedBy (b.lshr y exact)
      (LLVM.Byte.fromInt ((_root_.LLVM.Byte.toFrozenInt b).lshr (shiftAmount w y) exact)) := by
  sorry

/-- `llvm.bitcast` of a byte to an integer, at a nonzero width: freezing the poison bits refines
the integer, which is poison if any bit is. -/
private theorem byte_toInt_frozen {w : Nat} (hw : 0 < w) (b : LLVM.Byte w) :
    _root_.isRefinedBy b.toInt (_root_.LLVM.Byte.toFrozenInt b) := by
  sorry

/-- The pointer cast back from the address of an allocation refines it: it is the allocation's
pointer without its provenance. -/
private theorem ptrFromInt_toInt (mem : MemoryState) (p : Pointer) :
    LLVM.Ptr.isRefinedBy (.val p) (mem.ptrFromInt (LLVM.Ptr.toInt (.val p))) := by
  sorry

end Veir.LLVMToGMIR.CTreeProofs
