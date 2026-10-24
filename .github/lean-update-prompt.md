# Bump VeIR to Lean @TARGET@

You are working unattended in a checkout of VeIR
(https://github.com/opencompl/veir), a compiler infrastructure written in Lean 4.
The repository is pinned to `leanprover/lean4:@CURRENT@`. Your job is to move it
to `leanprover/lean4:@TARGET@` and fix everything the new toolchain breaks, so
that a maintainer can review and merge the result as a pull request.

Nobody will answer questions while you work. When you are unsure, choose the
conservative option and say so in the summary. You run in a GitHub Actions job
on VeIR's CI runner, inside CI's Nix shell, so every tool CI uses is on `PATH`
(Lean via elan, clang/LLVM/MLIR, lit, filecheck, llubi, alive-exec). The job
has no GitHub write access.

## Ground rules

- Work only in this checkout. Do **not** `git push`, open pull requests, or
  touch any remote; the workflow that started you does that from your commits.
- Commit your work on the current branch (one or a few commits, in the
  repository's `chore:`/`fix:` style). Edits to tracked files that you leave
  uncommitted are committed for you at the end; new files are not, so commit
  every file you add on purpose.
- Scratch files (reproducers, `#check`s) are named `LeanUpdateScratch*.lean`;
  build logs go to `/tmp`. Delete scratch files before committing, and look at
  `git status` before any `git add -A`.
- Never use `sorry`, `admit`, new `axiom`s, `native_decide` in place of a proof
  that used to work, `set_option ... false` to switch off a linter or check, or
  `@[implemented_by]` to dodge a proof. `sorry` and `trace_state` are fine while
  debugging, but none may remain when you finish.
- Never delete, skip, weaken, or `#guard_msgs`-rewrite a test or theorem
  statement to make it pass. If a test's *expected output* changes only because
  Lean's pretty printer or messages changed, update it and list it in the
  summary.
- Do not change build settings in `lakefile.*` unless the new Lean version
  strictly requires it (explain why). Never change anything under `.github/`.

## Prefer the smallest fix

Fix the code at the point of breakage the way upstream intends: renamed lemma →
new name, deprecated API → its replacement (never silence the deprecation
linter). Do not refactor, reformat or "improve" unrelated code; the diff should
read as a list of what Lean changed.

When a `grind`/`simp`/`omega` call newly fails, times out, or draws an
unused-argument warning, try these in order and stop at the first that works:

1. Drop hints that became unnecessary or harmful (`grind [h]` → `grind`;
   remove the arguments the unused-simp-args linter names).
2. Supply what is missing: add the lemmas that used to fire automatically
   (`grind [foo, bar]`), or, when `grind` blows up, find the exploding lemmas
   (`set_option trace.grind.ematch.instance true`, `grind?`) and exclude them
   with `grind [-lemma]`.
3. Restructure the proof (explicit `cases`/induction, intermediate `have`s), in
   the style of the neighbouring proofs.
4. Last resort: raise `maxHeartbeats` for that one declaration, at most 4× its
   current value, with a comment saying why.

Judge each step in the real file (`lake build --iofail <Module.Name>`), not
only in a scratch copy: a copy can behave differently (module system,
attributes and options in scope), so a step that fails there may still work.

When upstream now provides a lemma that the repository defines locally
("already declared" errors, or a hint the linter calls unused because upstream
tagged its own version), delete the local copy and use upstream's.

## Upstream bugs

If a failure looks like a Lean bug or regression rather than an intended
change:

- Search before working around it:
  `curl -s "https://api.github.com/search/issues?q=repo:leanprover/lean4+<keywords>"`
  (issues and PRs, open and closed; at most 10 searches a minute).
- Put `-- TODO(lean-bump): <what is broken> (lean4#NNNN)` at the workaround,
  or "no upstream issue found" instead of the number.
- If `UnitTest/LeanBugs.lean` exists, add a `#guard_msgs` test there that
  records the buggy behaviour, following the existing entries.
- List it under "Upstream issues" in the summary, with a minimal reproducer if
  you found no issue.

`UnitTest/LeanBugs.lean` is meant to fail when an upstream bug is fixed. If an
entry fails because the bug is gone, do what its comment says: turn it into a
success test and remove or simplify the workaround it points to. If the bug only
changed shape, update the expected message. Report either case prominently.

## Steps

1. **Toolchain files.** The workflow has already set every regular-file
   `lean-toolchain` to `@TARGET@` and committed that (see "Where you start").
2. **Dependencies.** VeIR's packages are local path dependencies, except the git
   dependency `Coinductive` (https://github.com/ISTA-PLV/coinductive,
   `inputRev = main`, no release tags), pinned in one or more
   `lake-manifest.json` files. Keep the pin unless it fails to build on
   @TARGET@. Then pick the newest commit on Coinductive's `main` whose
   `lean-toolchain` is not newer than @TARGET@ and set it in every manifest
   that pins it (`lake update Coinductive` in each package, same rev
   everywhere). Never fork, vendor or patch a dependency; if no compatible rev
   exists, stop and report it.
3. **Run the checks** with `bash @OUT@/checks.sh /tmp/checks` from the
   repository root. It runs what VeIR's CI runs and the workflow re-runs after
   you finish: `lake build --iofail`, `lake test --iofail`, `lit Test/ -v`,
   the `ExArray` and `QPFTypes` packages, `./Tools/check-*`, and a debug
   build. It writes a task list to `/tmp/checks/checks.md` and the output to
   `/tmp/checks/checks.log` (each check starts with a `===` line). It takes
   several minutes; while iterating, run single checks or modules instead.
   `--iofail` turns every warning into an error, so new linter warnings must
   be fixed too.
4. **Read what changed** when the build breaks in ways that are not obvious.
   Release notes: `https://lean-lang.org/doc/reference/latest/releases/v4.X.0/`
   for each minor version after @CURRENT@ up to @TARGET@ (`curl -sL`). For
   renamed or deprecated declarations, grep Lean's sources for `@[deprecated`:
   `git clone --depth 1 --branch @TARGET@ https://github.com/leanprover/lean4 /tmp/lean4`.
   Prefer this over guessing.
5. **Build and fix** until every check passes. Capture build output in a log
   under `/tmp` and read the first errors rather than everything. Lake's `✖`
   lines name failing modules, and `Some required targets logged failures:`
   lists them all. Fix the earliest failing module first; later errors are
   often consequences. `lake build --iofail <Module.Name>` iterates on one
   module. A full cold build takes a few minutes on this machine.
6. **Verify** by running the check script once more after your last edit.

## Budget and giving up

Spend your effort on real fixes. If after a serious attempt something still
does not build (a Lean regression, or a proof that needs a new idea), stop
working on it, commit the partially fixed state (never with `sorry`), and
describe the remaining failure precisely so a maintainer can pick it up. A
clear, honest, incomplete pull request is far more useful than a "green" one
that cheats.

## Summary (required)

Before you finish, write `LEAN_UPDATE_SUMMARY.md` in the repository root. Do
**not** commit it; the workflow uses it as the pull request body. Format:

```markdown
<!-- status: success | partial | failure -->
Bumps Lean from `@CURRENT@` to `@TARGET@`.

### Changes
Short bullets grouped by cause, e.g. "`List.foo` renamed to `List.bar`: 5
files". Mention every test expectation you changed.

### Upstream issues
Only if you worked around a Lean bug: link (or reproducer) and location.

### Remaining problems
Only if status is not `success`: the exact failing module or test, the error,
and what you tried.
```

Status: `success` if every check passed after your last change, `partial` if
you fixed some things but a check still fails, `failure` if you could not make
meaningful progress.
