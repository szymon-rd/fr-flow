# Reference: today's outputs

What today's FrFlow gives for each example, recorded before the rebuild (step 0 of section 9 of
`docs/redesign/ARCHITECTURE.md`). Each ported example's `PortSuite` and the `WalkthroughSuite` compare against it.
Nothing here is read by today's FrFlow.

## Re-running

```sh
python3 reference/capture.py rooms     # one example, or several: rooms auth keycloak crm sharing
python3 reference/capture.py           # all five
```

It needs sbt, Java and lake (Lean 4.35.0, as the examples' `lean-toolchain` says). It runs on a copy of the working
tree in `target/reference-copy`, so the examples are never written to. Each example is captured beside the copy and
replaces its directory here only once all of it is captured: a run that stops (a walk-through change that no longer
applies, an sbt error, a review that does not finish in 5 minutes) leaves the reference as it was. A re-run with
nothing changed gives no diff: the seed is fixed, the time zone is UTC, paths are relative and nothing records when
it ran. rooms takes about 6 minutes (its walk-through compiles three times), all five about 40 minutes, most of it
Lean and one JVM per command. The seeded bugs' generated cases use each knowledge base's own settings (seed 1), as
the suites do.

## What each example's directory holds

- `SOURCE`: the commit the capture was taken from (`-dirty` when a file it reads was not committed), the Lean
  toolchain and lake, and the seed: what to check out to rebuild the Lean here (`FrFlowGen` imports `lean/` and
  the example's `lean/Proofs`).
- `check.txt`: `check` from cold (none of FrFlow's derived files: no snapshot, no recorded checks or tests).
- `standings.txt` and `standings.tsv`: from `check --json`, also from cold (its exit code must be `check`'s), each
  node's kind, standing (proven, tested, assumed, failing, not proven; nothing to prove for a definition or design
  check has no result for, not checked for any other), check status, review state and causes, and the generated
  tests of its code as check recorded them (cases, against what, seed). The `.tsv` has those as fixed columns:
  `node kind standing status review causes cases against seed`.
- `seeds.txt`: the seeds the tests ran with (`FRFLOW_SEED=1`, the settings' default, for every check), with each
  test's cases; and the seeds fixed in the example's suites.
- `status.txt`, `tree.txt`, `show/NODE.txt`: those commands after the check.
- `review.txt`: `review --as demo-developer` on a terminal, every node skipped: nothing is decided or signed.
- `lean/`: the Lean `check` generated (`FrFlowGen`). The proofs written by hand stay in `examples/*/lean/Proofs`.
- `seeded-bugs.txt` (auth, keycloak, crm, sharing): each bug seeded as today's suite seeds it, and what stops it
  today: the `ContractViolation` on a call, the examples failing on the implementation, the generated case that
  fails (shrunk, with its seed, index and size). Those of section 9's table are marked; others the suites also seed
  are kept too. For sharing, the fault sweep and interleavings are the examples' runs, each verdict listed, and the
  suite's two scheduler faults (housekeeping not run, seeds 101 to 120 beside the kept runs 1 to 20; late wake-ups,
  `Random(7)`) with what each run measured.
- `rooms/walkthrough/`: the SQL query of a room's bookings forgetting the room (step 0, not in the README), then
  the README's rooms steps 4 to 6 (the calendar forgetting the next booking, the misread overlap, the misread
  reaching `covers`), each applied to the committed example on the copy: the change as a diff, then `check`,
  `status` and `review` after it. Each step starts from the committed example; step 6 includes step 5.

Every command's file ends with its stderr (when any) and its exit code. The walk-through's changes are written in
`capture.py` (`WALKTHROUGH`) as exact text to replace: when the rooms example changes so that one no longer applies,
the capture stops and names it.

The seeded bugs are run by `SeededBugs` in `reference/capture` (sbt project `referenceCapture`), which depends on
the examples; it is not a test and adds nothing to them.
