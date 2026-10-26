# Sources

The tags in `SKILL.md` and `rules.md` refer to the entries below. Each entry says
how the text was read for this skill, in October 2026. "Read" means the full
text, fetched from the author's own repository. "Excerpts" means search
results only, because the site could not be reached from the build
environment. "Book" means cited from the book without fetching it.

## The owner's direction

After the first version of this skill, the owner said: "we are aiming more
towards Typelevel-like / FP-like architecture than Li Haoyi / Simple Scala
style." What changed as a result:

- Services, boundaries and effectful programs are algebras over `F[_]` with
  separate interpreters, and programs take the least capability (A1 to A6). The
  first version used concrete `IO` and allowed `F[_]` only with two
  interpreters. `IO` is now fixed only in `IOApp`, in wiring and in tests.
- cats type classes and their laws are the vocabulary (T1 to T4, T10), every
  instance is law-tested with discipline, and every algebra has a law suite run
  against each interpreter (X1, X2).
- State, coordination and streaming use `Ref`, `Deferred`, `Queue`,
  `Dispatcher`, `Supervisor` and fs2 `Stream` (E4 to E7). Errors raised in `F`
  are `NoStackTrace` ADTs, and the channel follows who handles the error (R1,
  R2).
- Every domain value gets its own type with instances in its companion,
  following Volpe, which includes prose fields that could be swapped (D4).
- Typelevel's documentation, Volpe, *FPiS* and Ghosh are the primary sources.
  Odersky's "Lean Scala" and Li Haoyi's posts are secondary: they guide clarity
  inside a function (names, conciseness, least power), but not the
  architecture. The rule "take a function instead of an object with one
  method" was dropped, because effectful dependencies are now algebras.
- The rules on ADTs, illegal states, data versus interpreters, size budgets,
  one type per file, DSL design, views and comments are unchanged.

## Primary: Typelevel

- **[cats]** cats documentation, <https://typelevel.org/cats/>. *Read*
  (`typelevel/cats`, `docs`). Pages used: "Type classes" (the hierarchy and
  laws), "Law testing" (discipline rule sets in `cats.laws.discipline`, `Eq`
  and `Arbitrary` needed for law tests), "Guidelines" (instance placement and
  priority), "Validated" (accumulating errors), "Parallel" (monads describe
  dependent computations and applicatives independent ones), "ApplicativeError
  and MonadError", "Either", "EitherT", and "Motivations".
- **[CE]** cats-effect documentation, <https://typelevel.org/cats-effect/docs/>.
  *Read* (`typelevel/cats-effect`, `docs`). Pages used:
  - "Concepts" (an effect is a description; side effects are wrapped in
    `delay`, `blocking`, `interruptible` or `async`) **[CE concepts]**;
  - "Type classes" overview (capabilities in order of increasing power, with
    capturing side effects the most powerful) **[CE type classes]**, "Sync",
    "Temporal", "Clock" **[CE Clock]**;
  - "Resource" **[CE Resource]**, "Ref", "Deferred", "Queue", "Supervisor",
    "Dispatcher" (running effects from impure callbacks) **[CE Dispatcher]**,
    "Random" **[CE Random]** (together **[CE std]**);
  - "Thread model" **[CE thread model]**, "Tutorial" (written with polymorphic
    `F[_]: Sync` and `IO` only in `run`), and "FAQ" (`-Wnonunit-statement`,
    since a discarded `IO` never runs) **[CE FAQ]**.
- **[fs2]** fs2 guide, <https://fs2.io/#/guide>. *Read* (`typelevel/fs2`,
  `site/guide.md`). Taken: `Stream[F, A]` for incremental and unbounded data,
  and resource safety within streams.
- **[discipline]**, **[discipline-munit]** `typelevel/discipline` and
  `typelevel/discipline-munit` READMEs. *Read.* Taken: laws as `RuleSet`s
  checked with ScalaCheck; `checkAll` in a munit `DisciplineSuite`.
- **[Volpe]** Gabriel Volpe, *Practical FP in Scala*, 2nd ed., Leanpub. *Book*
  (chapters on tagless final, algebras, interpreters and programs, implicit
  and explicit parameters, newtypes and refinement types, error handling,
  modules, testing), and *read* the companion repository
  `gvolpe/pfps-shopping-cart`. Taken:
  - algebras as `trait Brands[F[_]]`, interpreters as
    `Brands.make[F[_]: GenUUID: MonadCancelThrow](postgres: Resource[F, Session[F]])`,
    programs as `Checkout[F[_]: Background: Logger: MonadThrow: Retry]` over
    explicit algebras;
  - capabilities such as `GenUUID[F]` and `Background[F]` with a summoner and
    an instance for `Sync` in the companion;
  - modules `Services`, `Programs`, `HttpApi` and `HttpClients`, each with one
    `make`, and `Main` as the composition root;
  - a newtype for every domain value with derived `Eq`, `Show` and codecs, and
    request types (`ItemNameParam`) kept apart from domain types (`ItemName`);
  - business errors as ADTs extending `NoStackTrace`, `adaptError` at
    boundaries;
  - law tests of instances (`checkAll("Monoid[Money]", MonoidTests[Money].monoid)`),
    and programs tested with in-memory interpreters.

## Primary: algebraic and type-driven design

- **[FPiS]** Michael Pilquist, Rúnar Bjarnason and Paul Chiusano, *Functional
  Programming in Scala*, 2nd ed., Manning, 2023. *Book*, with the exercise
  repository `fpinscala/fpinscala`. Taken: algebraic design in chapters 7 to 9
  (start from the operations and their laws, choose the representation later,
  keep a description separate from its interpreters); property-based testing
  in chapter 8; factoring effects out of pure code in chapter 13 ("inside every
  function with side effects is a pure function waiting to get out").
- **[Ghosh]** Debasish Ghosh, *Functional and Reactive Domain Modeling*,
  Manning, 2016, chapters 3 to 5. *Book*, and *excerpts* of his talk
  "Functional and Algebraic Domain Modeling". Taken: a domain module is an
  algebra (functions, types and laws) designed before and apart from its
  interpreters; modules compose; laws drive tests.
- **[Wlaschin]** Scott Wlaschin, "Designing with types" series, 2013, in
  particular "Making illegal states unrepresentable" and "Making state
  explicit", <https://fsharpforfunandprofit.com/series/designing-with-types/>.
  *Read* (`swlaschin/fsharpforfunandprofit.com`). Taken: the `Contact` example
  (two optional fields that encode "email or postal address" become a union);
  states and transitions as union cases instead of flags; wrapping primitives
  in single-case types. The phrase "make illegal states unrepresentable" is
  Yaron Minsky's.
- **[DMMF]** Scott Wlaschin, *Domain Modeling Made Functional*, Pragmatic
  Bookshelf, 2018. *Book.* Taken: types as documentation of the domain,
  workflows as functions, dependencies passed in as parameters, validation at
  the edge into trusted types.
- **[King]** Alexis King, "Parse, don't validate", 5 November 2019,
  <https://lexi-lambda.github.io/blog/2019/11/05/parse-don-t-validate/>.
  *Read* (`lexi-lambda/lexi-lambda.github.io`). Taken: use a data structure
  that makes illegal states unrepresentable; push the burden of proof upward
  to the boundary, but no further; let datatypes inform code ("avoid the
  temptation to just stick a `Bool` in a record"); avoid denormalized data;
  abstract types with smart constructors; total functions.
- **[Bernhardt]** Gary Bernhardt, "Boundaries" (SCNA 2012) and "Functional
  Core, Imperative Shell" (Destroy All Software screencast, 2012),
  <https://www.destroyallsoftware.com/talks/boundaries>. *Excerpts.* Taken:
  values as the boundaries between components; a pure core with a thin
  effectful shell; tests of the core without doubles.
- **[De Goes]** John A. De Goes, "The False Hope of Managing Effects with
  Tagless-Final in Scala", 2019, <https://degoes.net/articles/tagless-horror>.
  *Read* (`jdegoes/jdegoes.github.io`). His critique: premature indirection;
  `Sync` admits any side effect, so code requiring it gains no reasoning
  benefit ("Sync bloat"); many tagless-final type classes have no laws. This
  skill keeps tagless final at the owner's direction and turns the critique
  into constraints: programs never require `Sync` or `Async` (A3), every
  algebra has laws and a law suite (X2), and the core takes no `F` at all (E1).

## Primary: Scala language

- **[Scala 3 ref]** *Scala 3 Reference*, <https://docs.scala-lang.org/scala3/reference/>.
  *Read* (`scala/scala3`, `docs/_docs/reference`). Pages used: opaque type
  aliases (extension methods as an opaque type's public API), algebraic data
  types and enums, given instances ("canonical values"), using clauses,
  contextual abstractions (implicit conversions of "dubious value"), inline,
  macros, export clauses.
- **[Style guide]** *Scala Style Guide*, <https://docs.scala-lang.org/style/>.
  *Read* (`scala/docs.scala-lang`, `_style`). Taken: an explicit return type on
  every public member ("documentation checked by the compiler"); file naming;
  Scaladoc style.
- **[EffSc]** Marius Eriksen et al., *Effective Scala* (Twitter),
  <https://twitter.github.io/effectivescala/>. *Read*
  (`twitter/effectivescala`). Taken: reader first; return type annotations;
  implicits sparingly and never for conversions between similar types;
  `require` for API contracts and `assert` for invariants; case classes as
  ADTs; short orthogonal traits; visibility defines the public API; no
  exceptions for errors the caller must handle; "prefer 'obviously it works'
  to 'it works, obviously'".
- **[scalastyle]** scalastyle `default_config.xml`. *Read.* Its defaults (50
  lines per method, 8 parameters, 800-line files) are an outer reference for
  the budgets, which are tighter here.

## Secondary: local clarity

These guide code inside a function: names, conciseness, and the least powerful
construct that does the job. They do not decide the architecture.

- **[Odersky]** Martin Odersky, "Lean Scala", 11 April 2024,
  <https://odersky.github.io/blog/2024-04-11-post.html>. *Read*
  (`odersky/odersky.github.io`). Taken for local code: as concise as possible
  without losing clarity; no lingo or obscure features; implicit conversions
  and macros only when simpler means are not enough. Not taken: its preference
  for direct style over monadic effect systems, and for the core language over
  embedded DSLs, as architecture. No 2025 talk by Odersky titled "Simple Scala"
  was found.
- **[LiHaoyi-LP]** Li Haoyi, "Strategic Scala Style: Principle of Least Power",
  2016, <https://www.lihaoyi.com/post/StrategicScalaStylePrincipleofLeastPower.html>.
  *Excerpts.* Taken: the least powerful construct that solves the problem;
  immutability with mutation scoped narrowly; few, simple published entry
  points (S1). His ladder of dependency-injection options, with default
  arguments low on it, is cited from the post as remembered, because the
  excerpts stop before that section.
- **[LiHaoyi-TS]** "Strategic Scala Style: Practical Type Safety". *Excerpts*
  (section titles and introduction): structured data instead of strings, no
  integer enums or string flags, boxed ids.
- **[LiHaoyi-CN]** "Strategic Scala Style: Conciseness & Names". *Excerpts*: a
  name shows the reader something they want to know, and its length follows
  its scope.
- **[LiHaoyi-DD]** "Strategic Scala Style: Designing Datatypes". *Excerpts*:
  transparent case classes for data, and opaque classes for types with
  internal invariants.

## Existing skills

- **[VirtusLab]** VirtusLab, `scala-skill`, skill `direct-style-scala`,
  <https://github.com/VirtusLab/scala-skill>, commit `2b4d8d0` (16 October
  2026). *Read.* Licence: Apache-2.0, as declared in its `plugin.json`. Rules
  adapted from its "Coding style" and "Functional programming" sections and
  from the chapters "Code organization and visibility", "Domain modeling" and
  "Error handling": one concern per function; explicit return types; narrowest
  visibility; no class-level `var`; immutable collections; lawful APIs;
  opaque types for domain values; enums instead of `Boolean` parameters;
  `Either` smart constructors; typed errors; concept-named packages; targeted
  tests; zero warnings with `-Wunused:all`, `-Wvalue-discard` and
  `-Wnonunit-statement`. Its Ox, Tapir and direct-style material does not apply.
  The rules above are rewritten for cats-effect and tagless final.
- **antigravity** `skills/super-code/scala` and `skills/scala-pro` (MIT).
  *Read.* Nothing was adopted beyond the common advice against `.head` and
  `.get`, which F3 covers through King.
- **[Owner]** `docs/USAGE.md` in this repository: "One type to a file, in a
  package per concept". And the direction quoted at the top of this file.

### Notice for adapted material

Portions of `SKILL.md` and `rules.md` (the rules marked [VirtusLab]) are
adapted from VirtusLab `scala-skill`, licensed under the Apache License,
Version 2.0 (<https://www.apache.org/licenses/LICENSE-2.0>). They were
modified: rewritten for cats-effect and this repository, with new examples.
No text from that project is copied verbatim.

## Where the sources disagree

### Tagless final or concrete `IO` (A1 to A5)

- Volpe builds the application in tagless final, with algebras over `F[_]`,
  interpreters built by `make`, programs with capability constraints, and `IO`
  only in `Main`. The cats-effect documentation and tutorial write polymorphic
  `F[_]` code with `IO` only in `run`.
- De Goes recommends a concrete effect type for applications.
- Odersky's Lean Scala prefers direct style.

**Rule:** at the owner's direction, Volpe's layering. Every service, boundary
and effectful program is an algebra over `F[_]` with separate interpreters.
Programs require the least capability and never `Sync`, `Async` or `LiftIO`.
`IO` is fixed in `IOApp`, in wiring and in tests, or elsewhere with a stated
reason. **Reason:** interpreters can be swapped (in-memory for tests, live in
production), each algebra's laws can be checked against every interpreter,
and a program's constraints state what it can do. The constraint on `Sync`
answers De Goes's "Sync bloat".

### Direct style or monadic effects

**Rule:** monadic, with cats-effect and fs2 throughout. Odersky's direct style
is not used.

### The role of Odersky and Li Haoyi

Both write about architecture as well as style. **Rule:** they are secondary
sources for clarity inside a function. Architecture follows Typelevel, Volpe,
*FPiS* and Ghosh.

### Initial or final encoding of the DSL (A6)

*FPiS* and Ghosh use both encodings, and the Typelevel default for effects is
final. **Rule:** use an initial encoding (an ADT folded by interpreters) for
what FrFlow inspects, prints to Lean, hashes or rewrites: nodes and terms. Use
a final encoding for what is only run by several interpreters: user flows over
`F[_]`. **Reason:** a final encoding cannot be printed or hashed without
interpreting it into an initial one.

### Errors in `Either` or in `F` (R2)

VirtusLab returns `Either` for every recoverable failure. Volpe raises
`NoStackTrace` ADTs in `MonadThrow` and handles them where needed. The cats
documentation covers both. **Rule:** follow who handles the error. When the
caller branches on it, it goes in the result type (`F[Either[E, A]]`, composed
with `EitherT` inside a program). When nobody nearby handles it, it is raised
and reported at the edge.

### Example tests or laws (X1, X2, X5)

VirtusLab asks for targeted example tests. Typelevel checks laws with
discipline. **Rule:** both. Laws for every instance and every algebra, run
against every interpreter, and examples for scenarios.

### Wrapping primitives (D4)

Volpe gives every domain value a newtype. Li Haoyi wraps where it prevents real
mistakes. **Rule:** Volpe. That includes prose fields that a caller could swap
(`statement` and `why`).

### `require` (F7)

Effective Scala uses `require` for API contracts. VirtusLab forbids it for
recoverable failures. **Rule:** types first. `require` only for bugs in
FrFlow, and model errors as values collected by validation.

### Files (M3)

VirtusLab bundles a family of types in one file. Volpe puts an algebra and its
interpreter in one file. The owner's rule is one type to a file. **Rule:** the
owner's. An algebra's live interpreter is its companion's `make`, so it shares
the file. Other interpreters get their own files. Prefer `enum` for families of
cases.

### Default arguments (F6)

Li Haoyi treats default arguments as light dependency injection. VirtusLab and
Effective Scala pass dependencies explicitly. **Rule:** defaults only for
optional settings on published entry points. Algebras and capabilities are
never defaulted.

### Implicit conversions (T6)

The Scala 3 reference and Odersky discourage them. FrFlow lifts literals into
`Term`. **Rule:** literal lifting only, in one file.

### Braces

**Rule:** braceless, as the repository is written. Braces are fine for a
one-line partial function.
