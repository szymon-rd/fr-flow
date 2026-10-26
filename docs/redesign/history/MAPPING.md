# Where the revision log went

`ARCHITECTURE-r15-log.md` in this folder is the approved architecture as it was written: revision 15, laid over
revisions 1 to 14. `../ARCHITECTURE.md` says the same design top to bottom. This file lists every section of the log
and where its content now is, or why it was left in the log only. Section numbers on the right are the new document's.

## Front matter

| Old | Now |
|---|---|
| Title and path note (`r43-design/` and the rest mapped to `docs/redesign/`) | the file table at the top; paths written as they are in this repository |
| Revision summaries 7 to 15 (lines 6–59) | history, left in the log; what they decided is in sections 2–9 |
| Appendices list: `r43-deps.txt`, `r43-features.md`, `r43tools/` | the file table (`dependencies.txt`, `features.md`, `tools/`) |
| Appendices list: what the planned code shows, suite by suite | 1.4 (build, counts, budgets), the evidence beside each concept (2, 3, 4.8, 4.9) |
| Appendices list: `r43-spike/` and its Lean builds | 1.4, 3.8, 4.8 (`lean-spike/`, the revision-15 build); 10.3 (compile-time spike) |

## 1. Summary

| Old | Now |
|---|---|
| The diagnosis in plain words (8 points) | 1.1, condensed; Appendix B |
| The target in plain words (13 points) | 1.2 |
| Recommendation | 1.3 |

## 2. The current architecture

| Old | Now |
|---|---|
| 2.1 Modules as they are | Appendix B (module sizes as one paragraph) |
| 2.2 Concepts and where each is represented | left in the log: today's representations; summarised as P8 in Appendix B and in `features.md` |
| 2.3 Data flow, end to end (today's) | left in the log: a picture of today's code, which the rebuild replaces; 4.1 gives the new phases |
| 2.4 The dependency graph, measured | Appendix B (summary); details in `dependencies.txt` |
| 2.5 Problems P1–P17 | Appendix B (one line each, with where each is addressed); the full prose stays in the log |
| 2.6 What changed since the measurement | rooms: section 3; the step refutation: 4.7; keys counted as committed, superseded by the deciders' list: 6; `Cause.movedUnderCode`: 6 |

## 3. Sources

| Old | Now |
|---|---|
| Sources, and what the design takes from each | Appendix C (condensed; the URLs stay in the log); Kiselyov and CKS citations in 4.2 |

## 4. The target architecture

| Old | Now |
|---|---|
| 4.1 Concepts, each with its theory (fifteen) | spread over 2 (concepts), 4.2–4.9 (compiler), 5 (production's dependency); the numbered list is not repeated |
| 4.2 Phases and their types | 4.1 |
| 4.3 Modules and the direction of dependencies | 5 (graph, table); plain code and programs without ambient state: 2.2, 4.4, 4.9; state: 7.3 |
| 4.4 How a node is represented (field table) | 2.1, 4.5 (today's fields, condensed); the DSL forms in 2 |
| 4.4 An error waiting for its place | 4.5 |
| 4.5 Views are derived, and the API | 4.10 (views, API table); the snapshot: 6 |
| 4.6 Error model | 7.1 |
| 4.7 Effects: where `F[_]` is used | 7.2 |
| 4.8 The owner's decisions A–G and the rest | Appendix A; each applied where it acts (4.2, 4.4, 6, 8, 9) |
| 4.9 Decisions: content, deciders, signatures, fingerprints, review, rules | 6 (the mechanical rule and `Seals.signAdded` included) |
| 4.10 Patterns | 11 (the pattern table, with its example files) |
| 4.11 The planned code: reading guide table | 1.5 (a reading order of about twelve files); the full table stays in the log |
| 4.11 The Lean evidence (crm byte for byte) | 4.8 |
| 4.11 The program evidence (`RecordingSuite`, `RunningSuite`) | 4.4, 4.9 |
| 4.11 The term, calendar, whole-theory and testing evidence | 2.3–2.10, 3.5, 3.7, 3.8, 4.2 |
| 4.11 The Lean evidence for rooms | 1.4, 3.8 |
| 4.11 Measured (budgets, casts) | 1.4, 7.3 |
| 4.11 Size projection | 5; the per-revision line counts are history, left in the log |
| 4.12 What dropping run-time checking removes | 8 |
| 4.13 Terms in tagless-final style | 4.2 (algebras, interpreters, binders, the closed `Term`, hard constructs, notes, open vocabularies, the non-compositional needs, optimisation, laws); 4.3 (the IR); 3 (rooms' code) |
| 4.13 Revision paragraphs (what 8, 9, 10 changed) | history, left in the log |
| 4.13 Spike: compile time and error messages | 10.3; the JVM-limit defect: 10.1 |
| 4.14 The owner's core concepts: concept table | 2 (each concept with where it lives) |
| 4.14 Three kinds of nodes, what the removed kinds became | 2.1, 8 |
| 4.14 Two kinds of values | 2.2 |
| 4.14 Two quantifiers, `made_<maker>` | 2.3 |
| 4.14 A claim constrains what it mentions (obligations table) | 2.7 |
| 4.14 Edges | 2.4, 2.5 |
| 4.14 The world outside, atomicity | 2.6 |
| 4.14 Consistency | 2.8, 3.9 |
| 4.14 Vacuity | 2.9 |
| 4.14 Examples | 2.10 |
| 4.14 How a reader sees how each claim is checked | 3.8 |
| 4.14 Rooms, end to end | 3 |
| 4.14 Auth's purpose over Declarations | 2.2, 3.9 |
| 4.14 The `&&` guideline | 2.1, 2.3 |
| 4.14 What revisions 14 and 15 delete, add and cost | deleted: 8; added: 2; casts: 7.3; tactics: 4.8; the line deltas are history, left in the log |

## 5. Feature audit

| Old | Now |
|---|---|
| Feature audit summary | 8; the full table stays in `features.md` |

## 6. Rebuild plan

| Old | Now |
|---|---|
| Layout during the rebuild | 9 (layout) |
| What proves the new FrFlow does what the old one did | 9 (equivalence) |
| The rooms walk-through as a test | 9 (`WalkthroughSuite`) |
| Order: steps 0–15 | 9 (steps table and the paragraph after it) |
| The planned code's stubs, by step | 9 (stubs by step) |
| Seeded bugs, and what catches each | 9 (seeded bugs table) |
| Risks | 10.1 |

## 7. Rules that keep it from decaying

| Old | Now |
|---|---|
| Rules 1–9 | 11 |

## 8. Where each problem is addressed

| Old | Now |
|---|---|
| P1–P17 | Appendix B |

## 9. Changes in this revision

| Old | Now |
|---|---|
| Revision 15's findings table (R14.1–R14.8) | history, left in the log; each outcome is in 2 and 3 (one `Definition` type, written premises, `RoomBookings`, names, whole-formula tests, solving order, `implementProvided`) |
| Revisions 14 to 1: changes tables and paragraphs | history, left in the log |
| Test counts and build results quoted per revision | 1.4 gives revision 15's (147 tests, the Lean build) |

## Read from the planned code, not the log

The log's list of content fields (old 4.9) still named fields that revisions 14 and 15 removed (`examples`, `keeps`,
`expects`, `substitutions` and others). Section 6 lists the fields
`planned/src/project/frflow/project/pipeline/Contents.scala` makes. The `Problem` cases in 4.6 and the obligation
names in 4.7 are likewise those of the planned code.

## Not carried over

Kept only in the log: the full file-by-file reading guide of the planned code (old 4.11; 1.5 gives a reading order),
today's concept and data-flow tables (old 2.2, 2.3), the sources' URLs, the per-revision size deltas, and the
snapshot's row names.
