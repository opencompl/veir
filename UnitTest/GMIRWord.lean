module

import all Veir.Dialects.GMIR.Interpreter
import all Veir.Dialects.GMIR.OpInfo
import all Veir.Data.LLVM.Int.Basic
import all Veir.Interpreter.CTree
import all CTree.Defs

open Veir CTree

/-- The result of a word operation may have any upper word, including neither zero nor a
    copy of bit 31. Test the nondeterministic interpreter, not only its zero-extending runner. -/
example (msb : BitVec 32) (mem : MemoryState) :
    PureOrErr.CanInterpretTo
      (GMIR.interpretOpCTree .g_addw { nsw := false, nuw := false }
        #[IntegerType.signless 64] #[.int 64 (.val 0xffffffff), .int 64 (.val 0)] #[] mem)
      (.ok (#[.int 64 (.val (msb ++ 0xffffffff#32))], mem, none)) := by
  change PureOrErr.CanInterpretTo (CTree.bind (CTree.ret _) _) _
  rw [CTree.bind_ret]
  apply (PureOrErr.CanInterpretTo.tau_iff _ _ _).mpr
  exact ⟨msb, .ret _⟩
