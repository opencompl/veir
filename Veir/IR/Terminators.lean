module

public import Veir.OpCode

/-!
  Per-`OpCode` classification of which ops are terminators (must be
  the last op in a block when blocks live inside a region).

  Used by `Veir/Verifier.lean`'s per-region terminator presence
  check (Phase F.3 of `harness/regions-design.md`).

  Vacuous on dialects without region-using ops (i.e., all currently
  ported dialects as of 2026-05-17). Becomes meaningful at Phase F.5
  when `function.def` lands — its `function.return` is the terminator
  every function body must end with.

  Classification mirrors MLIR upstream's `Terminator` trait. Cf
  branches (`cf.br`, `cf.cond_br`) and LLVM branches/returns are
  terminators by MLIR convention; they currently use the
  `blockOperands` successor model in VEIR rather than living inside
  a region, so the check is a no-op for those today.
-/

namespace Veir

public section

/--
  Returns `true` if the op is a terminator. The verifier requires
  every block inside a region to end in a terminator op. Ops without
  this trait may appear anywhere within a block; ops with it must
  appear only at the end (and exactly one per block).
-/
def OpCode.isTerminator (op : OpCode) : Bool :=
  match op with
  -- LLVM branches and return (cf'-style); when LLVM ops eventually
  -- live inside a `llvm.func` region, these will be the terminators.
  | .llvm .br | .llvm .cond_br | .llvm .return => true
  -- Cf dialect: same story.
  | .cf .br | .cf .cond_br => true
  -- func.return: terminates a function.def body.
  | .func .return => true
  -- Everything else: not a terminator (per default in MLIR).
  -- Future: function.return when Phase G.1 Function dialect lands
  -- (it will be `OpCode.function .return` via a new inductive).
  | _ => false

end

end Veir
