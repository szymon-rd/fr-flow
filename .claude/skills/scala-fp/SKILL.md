---
name: scala-fp
description: Typelevel-style functional architecture and code rules for FrFlow's Scala 3 (cats, cats-effect, fs2, circe, http4s), with size budgets, a review checklist and a refactoring procedure. Use whenever you write, refactor or review Scala in this repository, including when you add a field, a case class, a function, an algebra or interpreter, a package or a module; change a core type such as `Node`, `KnowledgeBase`, `Term`, `SnapNode` or `Overview`; touch effects (`F[_]`, `IO`, `Resource`, `Ref`, `Stream`), errors, type class instances, laws, givens or the DSL; or audit code for quality.
---

# Scala FP in FrFlow

Use this skill for every Scala change in the repository. The rules below are
short. Each one has an id, and `references/rules.md` gives every rule with a
bad and good example and its source. Other files in `references/`:

- `review-checklist.md`: the file-by-file review pass and the finding format.
- `refactoring.md`: how to change a core type safely, with a plan for `Node`.
- `sources.md`: the sources, the owner's direction, where the sources disagree,
  and the licence notice for adapted material.
- `measure.py`: measures the size budgets (`python3 -I .claude/skills/scala-fp/references/measure.py`).

When you write code, apply the rules as you go and run `measure.py` on the
files you touched. When you review, follow `review-checklist.md`. When you
change a type that other modules use, follow `refactoring.md`.

## 1. What good looks like here

The owner's direction is a Typelevel-style functional architecture. FrFlow is a
DSL and a tool. A developer writes nodes in Scala, and FrFlow turns them into
data. Interpreters run on that data: Lean printing, evaluation, checking at run
time, the snapshot, the CLI and the web view. Around the data sit effectful
services and boundaries (the ledger, git, Lean's `lake`, the file system, HTTP).

- **The domain is data with a stated theory.** For every core type you can say
  in two sentences what it is, which cases it has and which operations it
  supports, with their laws. A type whose fields only make sense for some of
  its values is several types: an `enum` whose cases carry only their own data.
- **The types rule out the states the domain rules out.** Every domain value
  has its own type (an opaque type with its instances), and each fact is stored
  once.
- **Effects are algebras with interpreters.** A service or boundary is a
  `trait X[F[_]]`. Its interpreters (live, in-memory) are built by smart
  constructors, as a `Resource` when they hold something. Programs are
  polymorphic in `F` and ask for the least capability they need. `IO` is chosen
  once, in `main`.
- **cats is the vocabulary, and the laws hold.** Structure is expressed with
  `Functor`, `Applicative`, `Monad`, `Traverse`, `Foldable`, `Semigroup` and
  `Monoid`. Domain types carry `Eq`, `Show` and `Order` instances. Every
  instance and every algebra is checked against its laws with property tests.
- **Data and its interpreters are kept apart.** The pure core does not depend on
  any interpreter, on `cats.effect` or on a codec.
- **Functions are small and do one thing.** You can describe each function
  without the word "and".
- **The public surface is small**, and **features are consolidated** into
  concepts. A new feature never adds optional fields to a type that already
  exists.

The primary sources are Typelevel's own documentation (cats, cats-effect, fs2,
discipline), Volpe's *Practical FP in Scala*, *Functional Programming in Scala*
and Ghosh for algebraic design, and Wlaschin and King for types. Odersky's
"Lean Scala" and Li Haoyi's posts are secondary: they guide clarity inside a
function (names, conciseness, least power), but not the architecture. See
`references/sources.md`.

## 2. Rules

Severity in a review: **H** high, **M** medium, **L** low (see the checklist).
The source tags are expanded in `references/sources.md`.

### Domain modelling (D)

- **D1 (H)** One concept per type. If some fields apply only to some values (a
  `kind` field that decides which other fields are set), make it an `enum`
  whose cases hold only their own fields. [Wlaschin, King, EffSc]
- **D2 (H)** Make illegal states unrepresentable. The type enforces a rule such
  as "a definition has no parents": the `Definition` case has no `under`. A
  builder that rejects the combination with `require` is a finding. [Wlaschin, King]
- **D3 (H)** Store each fact once. A field that another field determines
  (`kind` together with `isInvariant = rule.isDefined`) is a finding. [King]
- **D4 (M)** Give every domain value its own opaque type, with a smart
  constructor and its instances (`Eq`, `Show`, `Order` where it is ordered) in
  the companion. This covers ids, names, hashes, paths, quantities, and prose
  fields that could be swapped (`statement` and `why`). Use `java.nio.file.Path`
  or an opaque `RelPath` for files, never `String`. [Volpe, Scala 3 ref: opaques]
- **D5 (M)** No stringly typed data and no sentinels (`""`, `-1`, `null`). Use an
  `enum`, `Option` or a case. [King, LiHaoyi-TS]
- **D6 (H)** Parse, don't validate. Turn input into precise types once, at the
  boundary. Smart constructors return `Either[E, A]`, or `ValidatedNec[E, A]`
  to collect every problem. [King, Volpe]
- **D7 (M)** An `Option` field means "may be absent in the domain". It never
  means "set only for some kinds" (D1) or "not computed yet" (D9). Domain case
  classes have no default field values. [Wlaschin, King]
- **D8 (M)** Replace a `Boolean` field or parameter with a two-case `enum` or a
  case of the ADT. [King, VirtusLab]
- **D9 (M)** Give lifecycle stages their own types (built, validated, checked).
  [Wlaschin]
- **D10 (M)** Use the collection that states the invariant: `NonEmptyList`,
  `NonEmptyChain`, `Map`, `Set`. [King, cats]
- **D11 (H)** Keep `Any`, `asInstanceOf` and `?` out of domain signatures. An
  untyped IR stays in one module, behind typed constructors, with each cast
  explained. [EffSc, King]
- **D12 (M)** Data is a `final case class` or an `enum`. A plain class with a
  private constructor is for an abstraction with internal invariants only.
  [LiHaoyi-DD]

### Data and behaviour (B)

- **B1 (H)** A core type holds its data and the essential operations that follow
  from its meaning. They are pure and total. [Ghosh, FPiS]
- **B2 (H)** Interpreters live outside the type, each in its own package:
  running, checking at run time, evaluating examples, printing for people or
  for Lean, codecs and persistence. [Ghosh, Volpe, FPiS]
- **B3 (H)** Dependencies point inward. A core package does not import
  `runtime`, `example`, `testing`, printing, `cats.effect` or a codec. [Volpe, Bernhardt]
- **B4 (M)** Design the algebra first: the operations and their laws, in
  Scaladoc and as property tests, before the representation. [FPiS ch. 7-9, Ghosh]
- **B5 (H)** Configuration of how something runs (sampling rate, report sink)
  belongs to the module that runs it, never to the concept being run. [DMMF]

### Architecture: algebras, interpreters, programs, modules (A)

- **A1 (H)** An effectful service or boundary is an algebra: `trait Ledger[F[_]]`,
  `trait Git[F[_]]`, `trait Lake[F[_]]`, `trait FrFlowApi[F[_]]`. Its operations
  take and return domain types in `F`. Keep it short and orthogonal. [Volpe, Ghosh, EffSc]
- **A2 (H)** Interpreters are built by smart constructors: the live one as
  `make` in the algebra's companion, others (in-memory over a `Ref`) in their
  own files. A constructor returns `F[X[F]]`, or `Resource[F, X[F]]` when the
  interpreter holds something. Only interpreters require `Sync` or `Async`.
  [Volpe, CE]
- **A3 (H)** A program is polymorphic in `F` and requires the least capability
  it uses: `Functor`, `Monad`, `MonadThrow`, `Parallel`, `Clock`, `Temporal`,
  `Concurrent`. A program never requires `Sync`, `Async` or `LiftIO`, because
  those let it capture any side effect. [Volpe, CE type classes, De Goes]
- **A4 (M)** Algebras are explicit parameters. Capabilities are context bounds,
  with a summoner (`def apply[F[_]](using x: X[F]): X[F] = x`) in the
  capability's companion. [Volpe]
- **A5 (M)** Modules wire: `Services[F]`, `Programs[F]` and `Api[F]` are each
  built by one `make`, and the composition root in `IOApp` builds them in one
  `Resource` and fixes `F = IO`. Concrete `IO` elsewhere needs a stated reason
  in a comment. [Volpe, CE]
- **A6 (M)** DSL encodings: use an initial encoding (an ADT and interpreters
  that fold it) for what FrFlow inspects, prints, hashes or rewrites, such as
  nodes and terms. Use a final (tagless) encoding where the program is only
  run, by several interpreters, such as user flows over `F[_]`. [FPiS, Ghosh]

### Type classes, instances and laws (T)

- **T1 (M)** Write structure with cats: `traverse`, `foldMap`, `mapN`,
  `parTraverse`, `flatTraverse` and `combineAll` instead of hand-written folds
  and accumulators. [cats]
- **T2 (M)** Use `Semigroup` and `Monoid` for values that combine (counts,
  reports, diagnostics), so combining is `|+|` or `combineAll`. [cats]
- **T3 (M)** Each domain type has the instances its meaning gives it (`Eq`,
  `Show`, `Order` when it is ordered, `Monoid` when it combines), in its
  companion. Compare domain values with `===`. [cats, Volpe]
- **T4 (H)** A given type class instance is canonical and lawful, and is
  law-tested (X1). An operation without laws is a named function, never an
  instance. [cats law testing, Scala 3 ref: givens]
- **T5 (M)** Coherence: one instance per type, in the companion of the type or
  the type class. No orphans and no local givens that shadow. [cats guidelines]
- **T6 (H)** Implicit conversions are only for DSL literal lifting, all in one
  file. Using one to hide an access, such as `Boundary[T] => T`, is a finding.
  [Scala 3 ref: contextual]
- **T7 (M)** Use `using` and context bounds for type classes, capabilities and
  typing witnesses only (A4). [Scala 3 ref: using]
- **T8 (M)** Use extension methods for the API of opaque types and for syntax,
  never to attach interpreters to a core type. [Scala 3 ref: opaques]
- **T9 (M)** Derive `Codec` on DTOs in `protocol` only. [Volpe]
- **T10 (L)** Use `EitherT`, `OptionT` or `Kleisli` inside a program when they
  make a chain of steps clearer. Keep them out of algebra signatures. [cats EitherT]

### Effects (E)

- **E1 (H)** The core is pure: `node`, `kb`, `term`, `types`, `vocabulary`, Lean
  printing and `check/analysis` take no `F` and perform no effect. [FPiS ch. 13, Bernhardt]
- **E2 (M)** A program reads its inputs once through algebras, then calls pure
  functions. [Bernhardt, Volpe]
- **E3 (H)** Side effects are suspended only in interpreters, with `Sync[F].delay`,
  `Sync[F].blocking` (file, process, network), `interruptible` or `Async[F].async`.
  [CE concepts, CE thread model]
- **E4 (H)** Every lifecycle is a `Resource`: processes, servers, locks,
  temporary directories, and background fibers (`Supervisor`, `background`).
  [CE Resource]
- **E5 (H)** State and coordination use cats-effect and fs2: `Ref` for shared
  state, `Deferred` for a one-time signal, `Queue` for producer and consumer,
  `Semaphore` or `Mutex` for exclusion, and an fs2 `Stream` for incremental or
  unbounded data (progress, process output). `AtomicReference` is for
  synchronous wrappers a user's program calls, with a comment. Neither goes in
  a data type. [CE std, fs2]
- **E6 (H)** Effects run only in `IOApp`. An impure callback calls into `F`
  through a `Dispatcher` held as a `Resource`. A synchronous bridge that cannot
  be avoided (the examples run while the model loads) is one named object, with
  a comment. [CE Dispatcher]
- **E7 (M)** Time, randomness and ids come from `Clock[F]`, `std.Random[F]` and
  `std.UUIDGen[F]`. [CE Clock, CE Random]
- **E8 (M)** Compile with `-Wnonunit-statement`, `-Wvalue-discard` and
  `-Wunused:all`, so a discarded `F` value is an error. [CE FAQ, VirtusLab]

### Errors (R)

- **R1 (M)** Each module's errors are an `enum` whose cases carry data. Errors
  raised in `F` extend `NoStackTrace`. No `String` errors. [Volpe, cats]
- **R2 (M)** Pick the channel by who handles the error. If the caller branches on
  it, put it in the result type: `F[Either[E, A]]` in the algebra, composed with
  `EitherT` inside a program. If nobody nearby handles it, raise it with
  `MonadThrow[F].raiseError`, recover with `recoverWith`, and report it at the
  edge. [cats ApplicativeError, Volpe]
- **R3 (M)** Accumulate independent validation errors with `ValidatedNec` or
  `EitherNec` and `parMapN`. [cats Validated, cats Parallel]
- **R4 (M)** An interpreter maps library errors into the module's ADT
  (`adaptError`). Turn errors into text only in `cli` and `web`. [Volpe]

### Functions (F)

- **F1 (M)** Each function computes one thing, or orchestrates a few named
  steps. [EffSc, VirtusLab]
- **F2 (M)** Keep within the budgets in section 3.
- **F3 (H)** Write total functions. Do not call `.head`, `.get` or `.last` on
  values that may be empty, and do not `throw` on "impossible" cases. [King]
- **F4 (L)** Use names in domain words that say what a function returns or does,
  with length following scope. [LiHaoyi-CN]
- **F5 (M)** Give an explicit return type to every public, `private[pkg]` and
  `given` member. [Style guide]
- **F6 (M)** Default arguments are allowed only for optional settings on
  published DSL or CLI entry points, never for collaborators or effects.
  [VirtusLab, EffSc]
- **F7 (H)** Use `require` and `assert` only for bugs in FrFlow. A mistake in a
  model is a compile error or a collected validation error naming the node.
  [EffSc, King, VirtusLab]
- **F8 (H)** No exceptions for control flow. [EffSc]
- **F9 (M)** A `var` lives inside a method, never in a class. Use immutable
  collections. [VirtusLab]

### Modules and packages (M)

- **M1 (H)** Write the module and package dependency graph down and keep to it.
  No package cycles. [Volpe]
- **M2 (M)** Name each package after a concept, never after a mechanism (no
  `util`, `common`, `Types.scala`). [VirtusLab]
- **M3 (L)** One top-level type per file, with its companion. The live
  interpreter is the companion's `make`, so an algebra and its live
  interpreter share a file. Prefer `enum` to a sealed trait. [Owner, Volpe]
- **M4 (M)** Use the narrowest visibility the call sites allow. Justify every
  `private[frflow]`. [EffSc, VirtusLab]
- **M5 (L)** Keep 3 to 15 files per package. [VirtusLab]
- **M6 (L)** Use `export` only in the facade the DSL user imports. [Scala 3 ref]

### DSL design (S)

- **S1 (M)** Keep the DSL's entry points few and orthogonal. [Odersky, LiHaoyi-LP]
- **S2 (H)** Each entry point builds one ADT case and returns that precise type.
  Fluent methods exist only on the cases they apply to. [Wlaschin, King]
- **S3 (M)** Use `inline` and macros only for compile-time information (source
  text, positions), and keep inline bodies short. [Scala 3 ref: inline]
- **S4 (H)** The DSL builds data and runs nothing (A6). [Ghosh, FPiS]

### Views and DTOs (V)

- **V1 (M)** A view is derived from the domain by one function. [King]
- **V2 (H)** A view keeps the domain's shape. A union stays a union (an `enum`
  with a JSON discriminator), never one flat record of optional fields.
  [Wlaschin, King]
- **V3 (M)** Group a view's fields into nested records by concept, and give the
  count records a `Monoid` (T2). [D1]
- **V4 (L)** A DTO default is only for reading older files, and says so.
- **V5 (L)** Display text is computed by the renderer, never stored on the DTO.

### Testing (X)

- **X1 (H)** Law-test every type class instance with discipline: `cats-laws`
  and `cats-kernel-laws` rule sets (`EqTests`, `OrderTests`, `MonoidTests`,
  `FunctorTests`, `TraverseTests`) through `discipline-munit`'s `checkAll`. The
  `Arbitrary` and `Cogen` instances live in one generators file per module.
  [cats law testing, discipline-munit]
- **X2 (H)** Every algebra has a property suite of its laws, run against every
  interpreter, live and in-memory. The DSL's algebras (refinement, term
  evaluation) have property tests with `munit-scalacheck`. [FPiS ch. 8, Ghosh, Volpe]
- **X3 (M)** Keep golden tests for output users see: CLI text, generated Lean,
  the JSON snapshot.
- **X4 (M)** Test values in and values out. Fakes are in-memory interpreters
  (A2), never mocks. Test `F` code with `munit-cats-effect`, and time with
  `TestControl`. [Bernhardt, CE]
- **X5 (L)** Each test covers one scenario, and its name states the property.
  [VirtusLab]

`cats-laws`, `cats-kernel-laws`, `discipline-munit`, `munit-scalacheck`,
`scalacheck` and `scalacheck-effect-munit` are not in `build.sbt` yet. Add them, as `Test` dependencies at versions matching cats and
munit, in the first change that writes such tests.

### Comments (C)

- **C1 (L)** Every public type and member has Scaladoc in domain words, with the
  laws of each operation of an algebra or instance.
- **C2 (L)** Comments describe the code as it is. History belongs in git.
- **C3 (L)** Do not defend the obvious or contrast with alternatives nobody
  would choose.
- **C4 (L)** Restructure code that needs a comment to explain how it works.
  Comments naming outside constraints (the JVM's 64 KB method limit) are good.
  [EffSc]

## 3. Size budgets (Z)

These are review triggers. Code over a budget is a finding (rule Z, or F2 for a
function) unless the exception applies. Measure with
`python3 -I .claude/skills/scala-fp/references/measure.py [paths] [--all|--summary]`.
It is approximate, so read the code it points at before you report.

| Budget | Limit | Exception |
|---|---|---|
| Fields per case class or enum case | 6 | none: group them by concept (V3) |
| Optional or defaulted fields per type | 2, each absent in the domain (D7) | wire compatibility in `protocol` (V4) |
| Explicit parameters per function (`using` and context bounds excluded) | 4 | DSL entry points that mirror the user's operation's arity (`expect(a, b, result, note)`) |
| Non-blank lines per `def` | 20 | one `match` over an ADT whose cases are at most 2 lines each |
| Nesting of blocks and lambdas | 3 levels | none (checked by reading) |
| Public members of a core type, or operations of an algebra | 8 | none (checked by reading) |
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

End with the themes the findings share, and with the core types and algebras
that need a new theory (section 5).

## 5. Changing a core type

The full procedure, with a worked plan for `Node` and one for a boundary, is in
`references/refactoring.md`. In short:

1. **Baseline.** Green `sbt test` (and `sbt leanTest` when Lean output is
   affected). Record the CLI golden files, the generated Lean and the `--json`
   snapshot of each example, and the `measure.py` output.
2. **Theory first.** Write in domain words what the concept is, its cases, its
   operations and their laws, and what it is not responsible for. For a service,
   write its algebra and laws. The owner approves it before any code.
3. **Types before code.** Write the new types, algebras and signatures with
   `???` bodies, and a table mapping each old field to its new place, or to its
   deletion with the reason. The owner approves the table.
4. **One concept per change.** One type and its direct dependents per commit.
5. **Delete before add.** Remove dead fields, duplicate state and unused
   features first, with tests green.
6. **Let the compiler drive.** Change the type and follow the errors outward.
   No adapter outlives the change that needs it.
7. **Preserve behaviour.** Tests and law suites pass, and the golden outputs are
   identical. Each intended change in output is listed and approved separately.
8. **Re-measure.** No new budget violations in the files you touched.

## 6. Where the sources disagree

The owner's direction decides the architecture rows. Details and reasons are in
`references/sources.md`.

| Question | Sources | Rule here |
|---|---|---|
| Tagless final or concrete `IO` | Volpe, the cats-effect docs and the CE tutorial write algebras and programs over `F[_]`; De Goes says to use a concrete effect in applications; Odersky prefers direct style | Algebras over `F[_]` with separate interpreters for every service, boundary and effectful program. Programs take the least capability and never `Sync` or `Async`. `IO` only in `IOApp`, in wiring and in tests, or with a stated reason (A1 to A5) |
| Direct style or monadic effects | Odersky, or Typelevel | Typelevel: cats-effect and fs2 throughout |
| Where Odersky and Li Haoyi apply | Lean Scala and Strategic Scala Style cover both architecture and local style | Local clarity only: names, conciseness, least power inside a function. Not the architecture |
| Initial or final encoding for the DSL | FPiS and Ghosh build both; tagless final is the Typelevel default for effects | Initial (ADT) for what FrFlow inspects, prints or hashes; final for programs that are only run (A6) |
| Errors in `Either` or in `F` | VirtusLab: `Either` always; Volpe: ADTs raised in `MonadThrow`; cats documents both | By who handles it: `F[Either[E, A]]` when the caller branches, `raiseError` of a `NoStackTrace` ADT otherwise (R2) |
| Example tests or laws | VirtusLab: targeted example tests; Typelevel: laws with discipline | Laws for every instance and algebra, examples for scenarios (X1, X2, X5) |
| Wrapping primitives | Volpe: newtypes for every domain value; Li Haoyi: when it prevents mistakes | Volpe: every domain value, including prose that could be swapped (D4) |
| `require` | Effective Scala uses it for API contracts; VirtusLab forbids it | Types first, `require` only for FrFlow bugs (F7) |
| Files | VirtusLab bundles type families; Volpe puts an algebra and its interpreter in one file; the owner allows one type per file | The owner's rule, with the live interpreter as the companion's `make` (M3) |
| Default arguments | Li Haoyi: light dependency injection; VirtusLab and Effective Scala: explicit | Only for optional settings on published entry points (F6) |
| Implicit conversions | The Scala 3 reference and Odersky discourage them | Only for DSL literal lifting (T6) |
