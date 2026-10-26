---
name: scala-fp
description: Rules, size budgets, a review checklist and a refactoring procedure for production Scala 3 functional code in FrFlow (cats, cats-effect, circe, http4s). Use whenever you write, refactor or review Scala in this repository, including when you add a field, a case class, a function, a package or a module; change a core type such as `Node`, `KnowledgeBase`, `Term`, `SnapNode` or `Overview`; touch effects (`IO`, `Resource`, `Ref`), errors, givens or the DSL; or audit code for quality.
---

# Scala FP in FrFlow

Use this skill for every Scala change in the repository. The rules below are
short. Each one has an id, and `references/rules.md` gives every rule with a
bad and good example and its source. Other files in `references/`:

- `review-checklist.md`: the file-by-file review pass and the finding format.
- `refactoring.md`: how to change a core type safely, with a plan for `Node`.
- `sources.md`: what each source says, where the sources disagree, and the
  licence notice for adapted material.
- `measure.py`: measures the size budgets (`python3 -I .claude/skills/scala-fp/references/measure.py`).

When you write code, apply the rules as you go and run `measure.py` on the
files you touched. When you review, follow `review-checklist.md`. When you
change a type that other modules use, follow `refactoring.md`.

## 1. What good looks like here

FrFlow is a DSL and a tool. A developer writes nodes in Scala, FrFlow turns them
into data, and interpreters run on that data: Lean printing, evaluation,
checking at run time, the snapshot, the CLI and the web view.

- **Each type is one concept from a stated theory.** For every core type you can
  say in two sentences what it is, which cases it has and which operations it
  supports. A type whose fields only make sense for some of its values is
  several types. Write it as an `enum` whose cases carry only their own data.
- **The types rule out the states the domain rules out.** No combination of
  fields needs a `require`, a `throw` or a `case _ =>` to be rejected later. Ids,
  paths, hashes and positions get their own types. Each fact is stored once.
- **Data and the interpreters of the data are kept apart.** A core type holds its
  data and the operations that follow from what it means. Running, printing,
  persistence and validation live in their own modules and depend on the core.
  The core never depends on them.
- **Effects stay at the edges.** The core is made of pure functions over
  immutable values. `IO` reads the inputs, calls the core and writes the
  results. Every side effect sits inside `IO`, and every resource that needs
  releasing is held by a `Resource`.
- **Functions are small and do one thing.** You can describe each function
  without the word "and". A function that orchestrates calls named steps.
- **The public surface is small.** Each package exposes what other packages use
  and nothing else. The DSL has few entry points, and each one builds one case
  of the data.
- **Features are consolidated.** A new feature extends an existing concept or
  adds a new one with its own theory. It does not add optional fields to a type
  that already exists.

This follows Odersky's "Lean Scala" (simple, no over-abstraction, least power),
Li Haoyi's Strategic Scala Style, Wlaschin's and King's type-driven design,
Bernhardt's functional core and imperative shell, and the algebraic design in
*Functional Programming in Scala*. See `references/sources.md`.

## 2. Rules

Severity in a review: **H** high, **M** medium, **L** low (see the checklist).
The source tags are expanded in `references/sources.md`.

### Domain modelling (D)

- **D1 (H)** One concept per type. If some fields apply only to some values (a
  `kind` field that decides which other fields are set), make it an `enum` or
  sealed ADT whose cases hold only their own fields. [Wlaschin, King, EffSc]
- **D2 (H)** Make illegal states unrepresentable. The type enforces a rule
  such as "a definition has no parents": the `Definition` case has no `under`.
  A builder that rejects the combination with `require` is a finding.
  [Wlaschin/Minsky, King]
- **D3 (H)** Store each fact once. Do not keep a field that another field
  determines (`kind` together with `isInvariant = rule.isDefined`). Compute
  derived values in functions. [King: denormalized data]
- **D4 (M)** Use opaque types for ids, names, hashes, relative paths and
  quantities, each with a constructor in its companion and extension methods
  for its operations. Use `java.nio.file.Path` or an opaque `RelPath` for files,
  never `String` or `List[String]`. [Scala 3 ref: opaques, LiHaoyi-TS, Volpe]
- **D5 (M)** No stringly typed data and no sentinels. Do not use `String` for
  kinds, statuses or source code, and do not use `""`, `-1` or `null` to mean
  absent. Use an `enum`, `Option` or a case. [LiHaoyi-TS, King]
- **D6 (H)** Parse, don't validate. Turn input (JSON, CLI arguments, DSL calls,
  files) into precise types once, at the boundary. Smart constructors return
  `Either[Error, A]`, and code inside the boundary takes the precise type. [King, Volpe]
- **D7 (M)** An `Option` field means "may be absent in the domain". It does not
  mean "set only for some kinds" (that is D1) or "not computed yet" (that is a
  separate stage type, D9). Domain case classes have no default field values.
  [Wlaschin, King]
- **D8 (M)** Replace a `Boolean` field or parameter with a two-case `enum`, or
  with the case of the ADT it distinguishes. [King, VirtusLab]
- **D9 (M)** Give lifecycle stages their own types: built, then validated, then
  checked. Do not use one type with `Option` fields that fill in over time.
  [Wlaschin: state machines]
- **D10 (M)** Use the collection that states the invariant: `NonEmptyList`,
  `Map` or `Set` for keyed or unique data. `distinctBy(System.identityHashCode)`
  means an id is missing. [King, cats]
- **D11 (H)** Keep `Any`, `asInstanceOf` and `?` out of domain signatures. If an
  untyped IR is needed, confine the casts to one module, behind typed
  constructors, and explain each cast in a comment. [EffSc, King]
- **D12 (M)** Write data as a `final case class` or an `enum`. Use a plain
  `class` with a private constructor only for an abstraction that has internal
  invariants, never for data with a hand-written `copy`. [LiHaoyi-DD]

### Data and behaviour (B)

- **B1 (H)** A core type holds data and its essential operations: the ones that
  follow from its meaning and that every user needs. They are pure and total.
  [Ghosh, FPiS]
- **B2 (H)** Interpreters live outside the type. Running, checking at run time,
  evaluating examples, printing for people or for Lean, codecs and persistence
  each sit in their own package, which depends on the core. [Ghosh, Volpe, Bernhardt]
- **B3 (H)** Dependencies point inward. A core package does not import
  `runtime`, `example`, `testing`, printing, `cats.effect` or a protocol codec.
  [Bernhardt, Volpe]
- **B4 (M)** Design the algebra first. Before you implement a type, write its
  operations and the laws they obey, in Scaladoc and as property tests. [FPiS ch. 7-9, Ghosh]
- **B5 (H)** Configuration of how something runs (sampling rate, report sink)
  belongs to the module that runs it. It is not a field of the concept being
  run. [Bernhardt, DMMF]

### Functions (F)

- **F1 (M)** Each function computes one thing, or orchestrates a short sequence
  of named steps. If its description needs "and", split it. [EffSc, VirtusLab]
- **F2 (M)** Keep within the budgets in section 3 for lines, parameters and
  nesting.
- **F3 (H)** Write total functions. Do not call `.head`, `.get` or `.last` on
  values that may be empty, and do not `throw` on "impossible" cases. If a case
  is impossible, fix the types (D2). [King]
- **F4 (L)** Use names in domain words that say what a function returns or does.
  Long names for wide scopes, short names for local ones. No `process`,
  `handle`, `util`, `helper` or `manager`. [LiHaoyi-CN]
- **F5 (M)** Give an explicit return type to every public, `private[pkg]` and
  `given` member. [Style guide, EffSc]
- **F6 (M)** Default arguments are allowed only for optional settings on
  published DSL or CLI entry points. Collaborators and effects are passed
  explicitly. Never write `report: Violation => Unit = Violation.log`. [EffSc DI, VirtusLab]
- **F7 (L)** When a function uses one method of an object, take a function
  instead. [LiHaoyi-LP, EffSc]
- **F8 (H)** Use `require` and `assert` only for internal invariants whose
  failure is a bug in FrFlow. When the developer writing a model can act on an
  error, it is a value: a compile error through the types if possible,
  otherwise an entry in the validation report naming the node. [EffSc, King, VirtusLab]
- **F9 (H)** The core does not use exceptions for control flow. Catch with
  `NonFatal` (or `attempt`) at the edge only. [EffSc]
- **F10 (M)** A `var` lives inside a method, never in a class. Use immutable
  collections. [LiHaoyi-LP, VirtusLab]

### Effects (E)

- **E1 (H)** The core is pure. `node`, `kb`, `term`, `types`, `vocabulary`,
  Lean printing and `check/analysis` do no I/O, read no clock and do no
  logging. [Bernhardt, FPiS ch. 13, De Goes]
- **E2 (M)** Use `IO` at the edges, read each input once and then call the core.
  `check.Inputs.read` is the pattern to follow. [Bernhardt, CE concepts]
- **E3 (H)** Every side effect is inside `IO.delay`, `IO.blocking` (for file,
  process and network I/O) or `IO.async`. [CE concepts, CE thread model]
- **E4 (H)** Anything that must be released (a process, a server, a stream, a
  temporary directory) is a `Resource`. [CE Resource]
- **E5 (H)** Shared mutable state in `IO` code is a `Ref`. Use
  `AtomicReference` only in synchronous code that a user's program calls, not
  in `IO` (such as the wrapper `service` returns), with a comment saying why.
  Never put either in a data type. [CE Ref, VirtusLab]
- **E6 (H)** Call `unsafeRun*` only in `IOApp`, `main` or one named bridge per
  module, with a comment. [CE]
- **E7 (M)** Pass the clock, randomness and id generation in explicitly, or read
  them once in `IO`. [VirtusLab]
- **E8 (M)** Use the concrete `IO` in application modules. Use `F[_]` only for
  an abstraction that has at least two interpreters in use and laws, such as
  user flows run against models and against real boundaries. See section 6.
  [De Goes, Volpe, CE tutorial]

### Errors (R)

- **R1 (M)** Each module's errors are an `enum` whose cases carry data. No
  `String` or `Throwable` in the error type of a domain signature. [EffSc, VirtusLab, Volpe]
- **R2 (M)** Pure code returns `Either[E, A]`. In `IO` code, use
  `IO[Either[E, A]]` when the caller decides what happens, and `raiseError` for
  failures nobody handles locally. [EffSc, cats Either]
- **R3 (M)** Accumulate independent validation errors with `ValidatedNec` or
  `EitherNec` and `parMapN`. Report all of them at once. [cats Validated]
- **R4 (M)** Convert errors at module boundaries: map a lower module's error
  into the caller's error type in the function that crosses the boundary.
  Turn errors into text only in `cli` and `web`. [Volpe, EffSc]

### Type classes and givens (T)

- **T1 (M)** Use a type class only when each type has one canonical instance
  and the operation is generic (`Codec`, `Eq`, `Show`, `Order`, `LeanType`).
  Otherwise pass a value or a function. [Scala 3 ref: givens, EffSc implicits]
- **T2 (M)** Coherence: one instance per type, defined in the companion of the
  type or of the type class. No orphan instances and no local givens that
  shadow others. [Scala 3 ref, cats guidelines]
- **T3 (H)** Use implicit conversions only for DSL literal lifting (a value to
  `Term`), all defined in one file. Using one to hide an access, such as
  `Boundary[T] => T`, is a finding. [Scala 3 ref: contextual, Odersky]
- **T4 (M)** Use `using` for context passed unchanged through many layers (a
  capability, a typing witness). Ordinary dependencies are constructor or
  function parameters. [Scala 3 ref, EffSc DI]
- **T5 (M)** Use extension methods for the API of opaque types and for syntax.
  Do not use them to attach interpreters to a core type in the core type's
  file. [Scala 3 ref: opaques]
- **T6 (M)** Derive `Codec` on the DTOs in `protocol`, and not on domain types.
  [Volpe]

### Modules and packages (M)

- **M1 (H)** Write the module dependency graph down and keep to it: `protocol`
  and `model` at the bottom, interpreters above them, front ends on top. No
  package cycles. [Volpe, Bernhardt]
- **M2 (M)** Name each package after a concept, never after a mechanism (no
  `util`, `common`, `helpers`, `Types.scala`, `Models.scala`). [VirtusLab]
- **M3 (L)** One top-level type per file, with its companion. Enum cases live
  inside the enum. Prefer an `enum` to a sealed trait, so the language rule (a
  sealed trait's cases share its file) and this rule agree. [Owner, Style guide]
- **M4 (M)** Start every declaration at the narrowest visibility the call sites
  allow (`private`, then `private[pkg]`). Treat `private[frflow]` as public
  within the project and justify it. [EffSc visibility, VirtusLab]
- **M5 (L)** Keep 3 to 15 files per package. Split a package by sub-concept, and
  fold a package of one or two files into its parent. [VirtusLab]
- **M6 (L)** Use `export` only in the one facade the DSL user imports
  (`frflow.*`). [Scala 3 ref: export]

### DSL design (S)

- **S1 (M)** The DSL is a published interface. Keep its entry points few and
  orthogonal. [LiHaoyi-LP, Odersky]
- **S2 (H)** Each entry point builds one ADT case and returns that precise type
  (`Node.contract(...): Contract[F]`). Fluent methods are defined only on the
  cases they apply to, so a misuse fails to compile. [Wlaschin, King]
- **S3 (M)** Use `inline` and macros only for what needs compile-time
  information (source text, positions). Keep an inline method short: it
  captures what it needs and calls a plain method. [Odersky, Scala 3 ref: inline]
- **S4 (H)** The DSL builds data and runs nothing. [Ghosh, FPiS]

### Views and DTOs (V)

- **V1 (M)** A view is derived from the domain by one function
  (`SnapNode.of(...)`). It is never built field by field in several places.
  [King]
- **V2 (H)** A view keeps the domain's shape. A union in the domain is a union
  in the view (an `enum`, with a discriminator in JSON). Do not flatten it into
  one record with many optional fields. [Wlaschin, King]
- **V3 (M)** Group the fields of a view into nested records by concept, each
  within the field budget. [D1]
- **V4 (L)** A DTO default is allowed only to read older files, and says so in
  its Scaladoc. [Volpe]
- **V5 (L)** Display text (`shownKind`, labels) is computed by the renderer. It
  is neither stored nor defined on the DTO. [B2]

### Testing (X)

- **X1 (M)** Test the algebra: write property tests of the laws of the core
  operations. [FPiS ch. 8, Ghosh]
- **X2 (M)** Keep golden tests for output users see: CLI text, generated Lean
  and the JSON snapshot. They are how a refactor shows it preserved behaviour.
- **X3 (M)** Test values in and values out. Do not test plumbing (that one
  function calls another), and do not use mocks. A fake is an in-memory
  implementation of the interface. [Bernhardt, EffSc DI]
- **X4 (L)** Each test covers one scenario, and its name states the property.
  [VirtusLab]

### Comments (C)

- **C1 (L)** Every public type and member has Scaladoc saying what it is in
  domain words, and why when that is not obvious. [EffSc, Style guide]
- **C2 (L)** Comments describe the code as it is. History (before, now,
  renamed, round numbers) belongs in git.
- **C3 (L)** Do not defend the obvious or contrast with alternatives nobody would
  choose. Name an alternative only when it is a real trap.
- **C4 (L)** A comment that explains how tangled code works is a reason to
  restructure the code. A comment naming an outside constraint (the JVM's 64 KB
  method limit) is good. [EffSc]

## 3. Size budgets (Z)

These are review triggers. Code over a budget is a finding (rule Z, or F2 for a
function) unless the exception applies. Measure with
`python3 -I .claude/skills/scala-fp/references/measure.py [paths] [--all|--summary]`.
It is approximate, so read the code it points at before you report.

| Budget | Limit | Exception |
|---|---|---|
| Fields per case class or enum case | 6 | none: group them by concept (V3) |
| Optional or defaulted fields per type | 2, each absent in the domain (D7) | wire compatibility in `protocol` (V4) |
| Explicit parameters per function (`using` excluded) | 4 | DSL entry points that mirror the user's operation's arity (`expect(a, b, result, note)`) |
| Non-blank lines per `def` | 20 | one `match` over an ADT whose cases are at most 2 lines each |
| Nesting of blocks and lambdas | 3 levels | none (checked by reading) |
| Public members of a core type | 8 | none (checked by reading) |
| Non-blank lines per file | 200 | none |
| Line width | 120 columns | none |
| Top-level types per file | 1, with its companion | none |
| Files per package | 3 to 15 | the facade package `frflow` |

The baseline when this skill was written (`measure.py --summary` on
`modules/*/src/main/scala`): 20 types over the field budget (largest
`SnapNode` 31, `Overview` 30, `Node` 24), 15 over the optional-field budget,
55 functions over 4 parameters, 51 functions over 20 lines (largest
`Eval.compile` 99), 4 files over 200 lines, 204 files wider than 120 columns,
and 3 packages over 15 files.

## 4. Reviewing

Follow `references/review-checklist.md`: run `measure.py` and the greps listed
there, go through the modules in dependency order, and check each file against
the rules. Report each finding on one line:

```
[H] modules/model/src/main/scala/frflow/node/Node.scala:14 D1 — Node holds six kinds' fields (24, 20 optional); kind decides which are set → enum Node with one case per kind
```

End with the themes the findings share, and with the core types that need a
new theory (section 5).

## 5. Changing a core type

The full procedure, with a worked plan for `Node`, is in
`references/refactoring.md`. In short:

1. **Baseline.** Green `sbt test` (and `sbt leanTest` when Lean output is
   affected). Record the CLI golden files, the generated Lean and the `--json`
   snapshot of each example, and the `measure.py` output.
2. **Theory first.** Write in domain words what the concept is, its cases, its
   operations and their laws, and what it is not responsible for. The owner
   approves it before any code.
3. **Types before code.** Write the new types and signatures with `???` bodies,
   and a table that maps each old field to its new place, or to its deletion
   with the reason. The owner approves the table.
4. **One concept per change.** One type and its direct dependents per commit.
   Unrelated cleanups go in other commits.
5. **Delete before add.** Remove dead fields, duplicate state and unused
   features first, with tests green, then introduce the new types.
6. **Let the compiler drive.** Change the type and follow the errors outward.
   Do not keep an adapter that preserves the old shape past the change that
   needs it.
7. **Preserve behaviour.** Tests pass and the golden outputs are identical. Each
   intended change in output is listed and approved separately.
8. **Re-measure.** No new budget violations in the files you touched.

## 6. Where the sources disagree

Details and reasons are in `references/sources.md`.

| Question | Sources | Rule here |
|---|---|---|
| Tagless final or concrete `IO` | Volpe and the CE tutorial use `F[_]: Sync`; De Goes says to use a concrete effect in applications; Odersky prefers direct style | Concrete `IO` at the edges, no effect type in the core, `F[_]` only with two or more interpreters and laws (E8) |
| Direct style or monadic effects | Odersky (Lean Scala) or Typelevel | FrFlow stays on cats-effect, and keeping `IO` at the edges keeps monadic code small |
| `require` | Effective Scala uses it for API contracts; VirtusLab forbids it | Types first, `require` only for FrFlow bugs, and model errors as values (F8) |
| Files | VirtusLab and the style guide allow a family of types in one file; the owner allows one type per file | The owner's rule, with enums so the cases sit inside the type (M3) |
| Default arguments | Li Haoyi ranks them as low-power dependency injection; VirtusLab and Effective Scala pass dependencies explicitly | Allowed for optional settings on published entry points only (F6) |
| Embedded DSLs | Odersky prefers the core language to DSLs | The DSL is the product: keep its surface small and its internals plain Scala (S1-S4) |
| Wrapping primitives | VirtusLab: always; Li Haoyi: when it prevents real mistakes | Wrap when two values could be confused or the value has an invariant. Prose (`statement`, `why`) stays `String` (D4) |
| Implicit conversions | Scala 3 reference and Odersky discourage them | Only for DSL literal lifting (T3) |
