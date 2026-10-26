# Review checklist

Use this to audit a module, a package or a diff. The output is a list of
findings, one per line, then a short summary. Rule ids refer to `SKILL.md`, and
the examples are in `rules.md`.

## Severity

- **H (high)**: the design is wrong in a way that spreads. The fix changes a
  type or a dependency, and callers change with it. Examples: a union of
  concepts in one type (D1), an illegal state the types allow (D2), duplicated
  state (D3), a core package depending on an interpreter or on `IO` (B3, E1), a
  side effect outside `IO` (E3), an unreleased resource (E4), shared mutable
  state outside a `Ref` (E5), exceptions as control flow in the core (F9), a
  flattened view of a union (V2), a builder that accepts calls it must then
  reject (S2).
- **M (medium)**: a local defect. The fix stays inside one file or one package.
  Examples: a function with several jobs (F1), a budget exceeded by more than
  half (F2), a stringly typed or primitive domain value (D4, D5), `String`
  errors (R1), visibility wider than its call sites need (M4), missing return
  types (F5), missing law tests for a core operation (X1).
- **L (low)**: readability. Examples: a budget exceeded by up to half (a def
  of 21 to 30 lines, a record of 7 to 9 fields), names (F4), comments (C1 to
  C4), line width, package size (M5), one type per file (M3).

A type over the field budget whose fields depend on a kind is H under D1,
whatever its size.

## Finding format

```
[SEVERITY] path:line RULE — what is wrong, with the evidence → the change, in one sentence
```

Examples:

```
[H] modules/model/src/main/scala/frflow/node/Node.scala:14 D1 — 24 fields for six kinds, 20 optional or defaulted; `kind` decides which are set → enum Node with a case per kind and a shared Statement
[H] modules/model/src/main/scala/frflow/node/Node.scala:4 B3 — node imports example.ExampleRuns and runtime.RunTimeChecks → move checkExamples and enforce to frflow.example and frflow.runtime
[H] modules/model/src/main/scala/frflow/node/Node.scala:23 D3 — isInvariant (rule.isDefined) restates kind → an Invariant case
[M] modules/model/src/main/scala/frflow/node/Node.scala:259 F1 — enforce: chooses the check, samples, caches assumptions, binds, runs, reports, throws (30 lines) → Check.of, AssumptionWatch, Call.run
[M] modules/model/src/main/scala/frflow/node/Node.scala:17 D4 — governs: List[String] and file: String are paths → RelPath
[M] modules/model/src/main/scala/frflow/node/Keep.scala:5 D1 — Keep(view = Some, exempt = "") or Keep(view = None, exempt = reason) → enum Keeping { Kept; Exempt }
[H] modules/protocol/src/main/scala/frflow/protocol/snapshot/SnapNode.scala:9 V2 — 31 fields, 27 optional or defaulted, one record for every kind → header + enum SnapBody + checks kept apart
[M] modules/api/src/main/scala/frflow/api/report/Overview.scala:9 V3 — 30 counts in one record → ReviewCounts, ProofCounts, TestCounts, RunCheckCounts
[H] modules/model/src/main/scala/frflow/boundary/Boundary.scala:44 T3 — Conversion[Boundary[T], T] hides an access → explicit .ops
[L] modules/model/src/main/scala/frflow/LeanPrinter.scala:1 Z — 341 non-blank lines (budget 200) → split by what is printed
```

Report a finding only after reading the code. `measure.py` and the greps point
at places to look and are not findings in themselves. Do not report the same
cause twice: if `Node` is a union (D1), its optional fields (D7) and its
`require`s (D2, F8) belong to that one finding, listed as evidence.

## Pass 0: measurements

Run from the repository root:

```sh
python3 -I .claude/skills/scala-fp/references/measure.py modules/<m>/src/main/scala          # over budget
python3 -I .claude/skills/scala-fp/references/measure.py modules/<m>/src/main/scala --summary
grep -rn "asInstanceOf\|isInstanceOf" modules/<m>/src/main --include=*.scala                    # D11
grep -rn "throw \|require(\|\.get\b\|\.head\b\|\.last\b" modules/<m>/src/main --include=*.scala   # F3 F8 F9
grep -rn "AtomicReference\|\bvar \|mutable\.\|unsafeRun" modules/<m>/src/main --include=*.scala  # E5 E6 F10
grep -rn "Conversion\[\|implicit \|given " modules/<m>/src/main --include=*.scala                # T1 to T3
grep -rn "Instant.now\|System.currentTimeMillis\|Random\|UUID.random" modules/<m>/src/main --include=*.scala  # E7
grep -rn "private\[frflow\]" modules/<m>/src/main --include=*.scala | wc -l                    # M4
grep -rh "^import frflow\." modules/<m>/src/main --include=*.scala \
  | sed 's/^import \(frflow\.[a-z]*\).*/\1/' | sort | uniq -c | sort -rn                      # B3 M1
```

Files in `model` open with chained package clauses (`package frflow` then
`package node`), so every member of `frflow` is visible without an import. The
import greps undercount for that reason. To find uses of an interpreter from a
core package, also grep for its object names, for example
`grep -rn "Wiring\.\|ExampleRuns\.\|RunTimeChecks\." modules/model/src/main/scala/frflow/{node,kb}`.

For `model`, also check the package graph (B3, M1). A core package must not
import `runtime`, `example`, `testing`, `program`, `cats.effect` or a printer:

```sh
for p in node kb term types vocabulary; do
  echo "== $p"; grep -rn "^import frflow\.\(runtime\|example\|testing\|program\)\|^import cats.effect" \
    modules/model/src/main/scala/frflow/$p
done
```

When this skill was written, this printed `example` and `runtime` imports in
`node` and `kb`, and `program` imports in `types` and `vocabulary`.

## Pass 1: order

Review the modules in dependency order, so a finding in a lower module is known
before its consequences show up above it: `protocol`, `model` (packages
`term`, `types`, `vocabulary`, `node`, `kb`, then `flow`, `boundary`,
`example`, `runtime`, `testing`, `program`, then the files in `frflow`),
`lean`, `ledger`, `check`, `api`, `cli`, `web`, `agent`.

## Pass 2: each file

For each top-level type, answer these questions in order. Each "no" is a
finding under the rule given.

**The concept**

1. Can you state in two sentences what this type is, in domain words, without
   "and"? (D1, B1)
2. Does every field apply to every value of the type? Look for a `kind` field,
   `Option` or defaulted fields set together, `Boolean` flags, and sentinels
   (`""`, `-1`, `Nil` meaning "not this kind"). (D1, D5, D7, D8)
3. Can the type hold a value the domain forbids? Look for `require`, `throw`,
   `case _ =>`, `.get` and `assert` that reject combinations. (D2, F3)
4. Is any field derivable from others, or stored again elsewhere? (D3)
5. Are ids, paths, hashes, positions and quantities their own types? (D4)
6. Is it a `final case class` or `enum`? Is a plain class justified by an
   internal invariant? (D12)
7. Are `Any`, `?` and casts kept out of its signatures? (D11)

**Data and behaviour**

8. Is each method an essential operation that follows from what the type means?
   Methods that run, print, persist, validate or configure are findings. (B1,
   B2, B5)
9. Does the file import only packages below it? (B3, M1)
10. Are the laws of its operations written down, and tested? (B4, X1)

**Functions** (for each `def`)

11. Can its job be described without "and"? (F1)
12. Is it within 20 lines, 4 parameters and 3 levels of nesting? (F2)
13. Is it total for its declared input type? (F3)
14. Does its name say what it returns or does? (F4)
15. If it is public or `private[pkg]`, does it have a return type? (F5)
16. Are its defaults limited to optional settings on a published entry point?
    (F6)
17. Is `require` used only for FrFlow bugs? (F8)

**Effects and errors**

18. If this is a core package, is it free of `IO`, the clock, files and logging?
    (E1)
19. Is every side effect inside `IO.delay`, `IO.blocking` or `IO.async`? Is
    every acquired thing a `Resource`? (E3, E4)
20. Is mutable state a `Ref`, or a commented `AtomicReference` in synchronous
    user-called code? Does `unsafeRun` appear outside the entry point? (E5, E6)
21. Are the errors an ADT? Are they converted where they cross a module, and
    rendered only in `cli` and `web`? (R1 to R4)
22. Is `F[_]` used only where at least two interpreters exist? (E8)

**Givens, modules, DSL, views**

23. Is each given canonical, in a companion, and the only instance for its
    type? Are conversions limited to literal lifting? (T1 to T3)
24. Is visibility as narrow as the call sites allow? (M4)
25. For a DSL entry point: does it return the precise case? Does it only build
    data? Is its inline part short? (S2 to S4)
26. For a view or DTO: is it built by one function, does it keep the domain's
    unions, are its fields grouped, and does it stay free of display text?
    (V1 to V5)

**Comments**

27. Does each public member have Scaladoc in domain words? Are the comments free
    of history and of defences of the obvious? (C1 to C4)

## Pass 3: summary

After the findings, write:

1. **Counts** by severity and by rule.
2. **Themes**: the three to five causes that most findings share. For example:
   "one class per DSL concept collects every feature's fields", or
   "interpreters attached to the data they interpret".
3. **Concepts to rebuild**: each core type that needs a new theory, with its
   two-sentence statement and the findings it resolves. These are the inputs to
   `refactoring.md`, step 2.
4. **Deletions**: features, fields and functions that nothing uses, or that
   duplicate another, to remove first (`refactoring.md`, step 5).

## Reviewing a diff

For a change in progress, run passes 0 and 2 on the files the diff touches.
Report findings on the new and changed lines, plus any older finding the change
makes worse (another field on a type already over budget, another `require` in
a builder). Do not ask for unrelated cleanups in the same change.
