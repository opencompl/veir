# DCE refinement proof (unported)

Snapshot of Mathieu Fehr's `math-fehr/dce-proof` branch, commit `d75cc1a87` ("Proved DCE",
2026-10-26), branched from main at `53d57c2ac`. It proves that the `dce` pass refines the
module: `DCEPass.transform_isModuleRefinedBy` in `Veir/Passes/DCE/ModuleRefinement.lean`.

The files here are **not built**: this folder is outside every `lean_lib` root. They are kept as the
source for a port onto the current CTree framework, which they predate by about 200 commits of main
and by the end-to-end Puddle proofs and the branch-lowering refinement now on this branch.

## What is here

- `Veir/Passes/DCE/`: the proof, from erasure traces and macro steps up to module refinement.
- `Veir/Interpreter/CTreeRefinement.lean` and `Veir/Interpreter/CTreeRefinement/`: the refinement
  framework the proof is written against. It assumes three axioms that the current tree proves
  under its own definitions, so a port should discharge them rather than carry them over:
  - `refines_ub` (`CTreeRefinement.lean`): now the `CTree.Sim.ub` rule;
  - `refines_iter` (`CTreeRefinement/Iteration.lean`): now `CTree.Sim.iter`;
  - `operation_monotonicity` (`CTreeRefinement/Monotonicity.lean`): now
    `OpCode.interpretOp'Monotone_of_monotoneProved` and the per-dialect CTree monotonicity proofs.

## What is deliberately left out

The branch also carried an earlier generation of the RISC-V instruction-selection validity proofs
(`Veir/Passes/InstructionSelection/RISCV64*Validity.lean`) and of the Puddle CTree validity
(`Veir/PatternRewriter/Puddle/CTreeValidity.lean`, `CTreeSymbolicValidity.lean`,
`DriverPreservation.lean`). Both were superseded by what is on this branch and are not copied.

## Upstream files the branch modified

The proof also depends on the branch's versions of these files, which were not copied because the
current tree has moved on. Consult them with `git show d75cc1a87:<path>`:

- `UnitTest.lean`
- `UnitTest/Puddle.lean`
- `UnitTest/SideEffectInterfaces.lean`
- `Veir.lean`
- `Veir/Dialects/LLVM/Interpreter.lean`
- `Veir/Dialects/LLVM/OpInfo.lean`
- `Veir/Interfaces/DeadCodeInterfaces.lean`
- `Veir/Interpreter.lean`
- `Veir/Interpreter/CTree.lean`
- `Veir/Interpreter/CTreeInterpreter.lean`
- `Veir/Interpreter/Interp.lean`
- `Veir/Interpreter/Memory.lean`
- `Veir/Passes/DCE/dce.lean`
- `Veir/Passes/InstructionSelection/RISCV64.lean`
- `lean-ctrees/CTree/Sim.lean`

The `dce.lean` change itself, factoring the pure transformation out as `DCEPass.transform` so the
proof can refer to it, is small and should be redone on the current pass.
