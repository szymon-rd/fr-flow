# Agent report: FrFlow MVP

Date: 2026-10-21. Author: Claude (Opus 5.5), working in a Claude chat sandbox.

## Scope

This is the first implementation of the architecture from the design
discussion: a Scala framework that develops software as a tree of theory
nodes, where each child refines its parent and every refinement link is proven
in Lean 4. The example is an authorization platform whose root statement is
"no unauthorized user can access the system".

## What was built

| Component | Location | Content |
|---|---|---|
| Lean kernel (trusted base) | `lean/FrFlow/` | `Spec`, `Reach`, `Invariant`; `Refinement` with stuttering, plus `reach`, `invariant`, `transfer` (safety transfer) and `trans` (composition); event machines; `Machine.refinement` and `Machine.invariant`, which assemble per-event obligations |
| Theory model | `modules/core/.../model` | nodes, links (`abs`, `glue`), events with separate `assume` (environment) and `check` (implementation) clauses, invariants, assumptions, vocabulary |
| DSL | `.../dsl` | `TheoryDef`, `root`, `refine`, `event(...).params.assume.check.act.refines/refinesSkip` |
| Obligation generator | `.../obligation` | `init_<I>`, `<e>_inv_<I>`, `init_abs`, `<e>_grd`, `<e>_sim`, `<e>_skip` |
| Lean renderer | `.../render` | Vocab, Model, Obligations and Assembly modules per node, axiom-audit scripts, proof scaffolds |
| Lints | `.../lint` | statement length and sentence limits, child-count limit, reserved names, refinement targets, cited assumptions, unrefined parent events |
| Checker | `.../check` | lake build, attribution of diagnostics to obligations, exact-statement enforcement, forbidden constructs, assembly build, `#print axioms` audit |
| Ledger | `.../ledger` | approvals bound to spec hashes; check results bound to check hashes (stale detection) |
| Reports | `.../report` | status table, per-node slice for agents, `THEORY.md` digest |
| CLI | `.../cli` | `lint`, `render`, `scaffold`, `check`, `status`, `approve`, `slice`, `digest` |
| Example | `examples/authz` | T0 NoUnauthorizedAccess → T1 AuthnThenAuthz (assumption A1), authored proofs, generated Lean, ledger, slices, digest |

## Verification performed

All of the following were run in the sandbox with Lean 4.35.0, Scala 3.10.0
and JDK 21.

- **Lean kernel:** builds with no `sorry`.
- **Example check:**
  - T0 is proven, 3/3 obligations.
  - T1 is proven, 7/7 obligations.
  - The axiom audit of `Authz.T1.refinement` and `Authz.T1.inherits_T0_Safe`
    reports only `propext` and `Quot.sound`.
- **Scala compilation:** the sources compile with
  `-deprecation -feature -Werror`.
- **Tests:** 31 pass, 0 fail.
  - The unit suites cover obligations, the renderer, lints, the proof auditor,
    diagnostics and JSON/ledger.
  - The integration suite runs against Lean. It confirms that:
    - the example is proven end to end;
    - an event that bypasses the policy check fails its guard obligation;
    - a proof of a weakened statement is rejected;
    - `sorry` leaves an obligation open, and the child node waits for its
      parent;
    - a reworded statement invalidates only that node's approval.
- **Fixture coverage:** the `CounterTheory` fixture was additionally checked
  in Lean to cover edge cases: events without parameters, an empty witness
  `{}`, a gluing invariant, and an assumed clause. Both of its nodes are
  proven.
- **Manual negative checks:** an inserted `axiom` is reported as a file-level
  failure; a proof stating `True` instead of `Obl.<name>` is rejected.

## Not verified

- **sbt build.** Maven repositories were blocked by the sandbox network
  policy. After network access was widened, Maven Central returned HTTP 429.
  Compilation and tests therefore ran with the plain Scala distribution
  (`scripts/build-offline.sh`) and a local stand-in for the munit `FunSuite`
  API subset, which is not committed. The `munit` 1.1.1 and sbt 1.10.7
  versions in `build.sbt` and `project/build.properties` have not been
  resolved; run `sbt test` to confirm them.
- **Approvals.** The committed ledger contains check results only. Approval
  is meant to be a human act: run `approve T0 --by <name>` and
  `approve T1 --by <name>` after reviewing the statements.

## Design decisions made during implementation

- **Assumptions are guard clauses, not hypotheses over all states.** An
  assumption stated as a universally quantified premise is usually false for
  some state of the model, which makes every obligation that uses it vacuous.
  Placing assumptions in guards (`assume` clauses) restricts environment
  behavior instead, and keeps the guarantees meaningful.
- **Per-event obligations, assembled by the kernel.** Obligations are small
  and independent, so their status can be reported individually. Only
  `Machine.refinement` and `Machine.invariant` connect them to kernel
  theorems.
- **Statement enforcement in two layers.** A static check requires each
  theorem header to be exactly `Obl.<name>`. The assembly build then consumes
  each proof at its obligation type.
- **Lean fragments in the IR.** Model expressions are Lean source checked by
  Lean, not parsed by FrFlow. A typed expression IR (for semantic diffs) is
  future work.
- **Generated files are committed.** This keeps the Lean model reviewable in
  pull requests. Proof files are the only authored Lean.

## Suggested next steps

1. Run `sbt test` in an environment with Maven access, and add a GitHub Actions
   workflow that installs Lean and runs it.
2. Write a traceability compiler plugin for `@implements` / `@refines`, with
   detection of code that no node justifies.
3. Build an MCP agent interface with role-restricted operations, gated by the
   checker and by approvals.
4. Extend the example: T2a (authentication, discharging A1 under signature
   unforgeability), T2b (RBAC), and T2c (complete mediation, including the
   decision-cache conflict described in the design).
