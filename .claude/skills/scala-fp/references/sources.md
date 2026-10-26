# Sources

The tags in `SKILL.md` and `rules.md` refer to the entries below. Each entry says
how the text was read for this skill, in October 2026. "Read" means the full
text, fetched from the author's own repository. "Excerpts" means search
results only, because the site could not be reached from the build
environment. "Book" means cited from the book without fetching it.

## Scala

- **[Odersky]** Martin Odersky, "Lean Scala", 11 April 2024,
  <https://odersky.github.io/blog/2024-04-11-post.html>. *Read* (source in
  `odersky/odersky.github.io`). Taken: lean code is simple, as concise as
  possible without losing clarity, and free of lingo, over-abstraction and
  obscure features. Also: the Principle of Least Power applied to language
  features (implicit conversions and macros only when simpler means are not
  enough); immutable first without dogma; Scala 3 constructs only; the core
  language preferred to embedded DSLs; direct style preferred to monadic effect
  systems. No 2025 talk by Odersky titled "Simple Scala" was found. His Scalar
  2025 talk "Evolving Scala" covers the language's direction and gives no
  style rules.
- **[Scala 3 ref]** *Scala 3 Reference*, <https://docs.scala-lang.org/scala3/reference/>.
  *Read* (`scala/scala3`, `docs/_docs/reference`). Pages used: opaque type
  aliases (abstraction without overhead; extension methods as an opaque type's
  public API), algebraic data types and enums, given instances ("canonical
  values"), using clauses, contextual abstractions (its critique of implicits:
  overuse, conversions of "dubious value", hidden imports), inline, macros,
  export clauses.
- **[Style guide]** *Scala Style Guide*, <https://docs.scala-lang.org/style/>.
  *Read* (`scala/docs.scala-lang`, `_style`). Taken: an explicit return type on
  every public member ("documentation checked by the compiler"); file naming,
  and a sealed type's subclasses in its file; Scaladoc style. The guide calls
  itself "a list of rules to be broken".
- **[LiHaoyi-LP]** Li Haoyi, "Strategic Scala Style: Principle of Least Power",
  2016, <https://www.lihaoyi.com/post/StrategicScalaStylePrincipleofLeastPower.html>.
  *Excerpts.* Taken: choose the least powerful solution that solves the
  problem; immutability by default, with mutation scoped as narrowly as
  possible; simple published interfaces with standard types, and a function
  instead of an object with one method; case classes to bundle data and sealed
  traits for alternatives; a ladder of dependency-injection options from least
  to most powerful, in which default arguments sit low. The excerpts stop before
  the dependency-injection section, so that ladder is cited from the post as
  remembered and should be checked against the page.
- **[LiHaoyi-TS]** Li Haoyi, "Strategic Scala Style: Practical Type Safety",
  <https://www.lihaoyi.com/post/StrategicScalaStylePracticalTypeSafety.html>.
  *Excerpts* (section titles and introduction). Taken: avoid strings in favour
  of structured data, encode invariants in types, avoid integer enums and string
  flags, box integer ids.
- **[LiHaoyi-CN]** Li Haoyi, "Strategic Scala Style: Conciseness & Names",
  <https://www.lihaoyi.com/post/StrategicScalaStyleConcisenessNames.html>.
  *Excerpts.* Taken: a name shows the reader something they do not already know
  and want to know, and its length follows its scope.
- **[LiHaoyi-DD]** Li Haoyi, "Strategic Scala Style: Designing Datatypes",
  <https://www.lihaoyi.com/post/StrategicScalaStyleDesigningDatatypes.html>.
  *Excerpts.* Taken: transparent case classes for simple data, and opaque
  classes for types with internal invariants.
- **[EffSc]** Marius Eriksen et al., *Effective Scala* (Twitter),
  <https://twitter.github.io/effectivescala/>. *Read*
  (`twitter/effectivescala`). Taken: think of the reader after correctness;
  avoid type-level cleverness in production code; return type annotations on
  public methods; implicits used sparingly and never for conversions between
  similar types; `require` for API contracts and `assert` for invariants; case
  classes as ADTs; constructor dependency injection and functions instead of
  factory types; short orthogonal traits; visibility defines the public API;
  no exceptions for errors the programmer must handle; `NonFatal`; "prefer
  'obviously it works' to 'it works, obviously'".
- **[scalastyle]** scalastyle `default_config.xml`
  (`scalastyle/scalastyle`). *Read.* Its defaults (methods up to 50 lines, 8
  parameters, files up to 800 lines, 30 methods per type, cyclomatic complexity
  10) serve as an outer reference for the budgets, which are tighter here.

## Typelevel

Typelevel publishes no project-wide style guide. Its guidance is in the cats
guidelines and the cats-effect documentation, used here.

- **[CE concepts]** cats-effect, "Concepts",
  <https://typelevel.org/cats-effect/docs/concepts>. *Read*
  (`typelevel/cats-effect`, `docs`). Taken: an effect is a description and a
  side effect just happens; every side effect is wrapped in `IO(...)`,
  `IO.blocking`, `IO.interruptible` or `IO.async`.
- **[CE Resource]**, **[CE Ref]**, **[CE thread model]**, **[CE tutorial]**,
  **[CE FAQ]**: the pages "Resource" (acquire and release composed without
  nesting `bracket`), "Ref" (a purely functional wrapper over an
  `AtomicReference`), "Thread model" (blocking work on the blocking pool),
  "Tutorial" (written with polymorphic `F[_]: Sync`, with `IO` only in `run`),
  and "FAQ" (recommends `-Wnonunit-statement`, since a discarded `IO` never
  runs). *Read.*
- **[cats]** cats documentation: "Guidelines" (instance placement and
  priority), "Type classes", "Validated" (accumulating errors), "Either".
  *Read* (`typelevel/cats`, `docs`).

## Domain modelling and design

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
  workflows as functions from inputs to events, dependencies passed in as
  parameters, validation at the edge into trusted types.
- **[King]** Alexis King, "Parse, don't validate", 5 November 2019,
  <https://lexi-lambda.github.io/blog/2019/11/05/parse-don-t-validate/>.
  *Read* (`lexi-lambda/lexi-lambda.github.io`). Taken: use a data structure
  that makes illegal states unrepresentable; push the burden of proof upward
  to the boundary, but no further; let datatypes inform code ("avoid the
  temptation to just stick a `Bool` in a record"); avoid denormalized data and
  keep any you need behind one module; abstract types with smart constructors
  when a property cannot be encoded; turn partial functions total; treat the
  remaining "impossible" cases as radioactive.
- **[Ghosh]** Debasish Ghosh, *Functional and Reactive Domain Modeling*,
  Manning, 2016, chapters 3 to 5. *Book*, and *excerpts* of his talk
  "Functional and Algebraic Domain Modeling". Taken: a domain module is an
  algebra (functions, types and laws) designed before and apart from its
  interpreters; modules compose; laws drive tests.
- **[Volpe]** Gabriel Volpe, *Practical FP in Scala*, 2nd ed., Leanpub. *Book*
  (chapters on tagless final, algebras, interpreters and programs, newtypes and
  refinement types, error handling), and *read* the companion repository
  `gvolpe/pfps-shopping-cart`. Taken: algebras, interpreters and programs as
  separate layers (`domain`, `services`, `programs`, `http`); newtypes for
  every domain value; request types (`ItemNameParam`) kept apart from domain
  types (`ItemName`); error ADTs per layer; effect-polymorphic `F[_]` with
  capability type classes.
- **[Bernhardt]** Gary Bernhardt, "Boundaries" (SCNA 2012) and "Functional
  Core, Imperative Shell" (Destroy All Software screencast, 2012),
  <https://www.destroyallsoftware.com/talks/boundaries>. *Excerpts* (summaries
  and an interview). Taken: plain values as the boundaries between components;
  a functional core that takes values and returns values; a thin imperative
  shell for input, output and state; tests of the core without doubles.
- **[FPiS]** Paul Chiusano, Rúnar Bjarnason (and Michael Pilquist for the
  Scala 3 edition), *Functional Programming in Scala*, 2nd ed., Manning, 2023.
  *Book*, with the exercise repository `fpinscala/fpinscala`. Taken: algebraic
  design in chapters 7 to 9 (start from the operations and their laws, choose
  the representation later, and keep a description separate from its
  interpreters); property-based testing in chapter 8; factoring effects out of
  pure code in chapter 13 ("inside every function with side effects is a pure
  function waiting to get out").
- **[De Goes]** John A. De Goes, "The False Hope of Managing Effects with
  Tagless-Final in Scala", 2019, <https://degoes.net/articles/tagless-horror>.
  *Read* (`jdegoes/jdegoes.github.io`). Taken: for applications, tagless final
  is premature indirection; `Sync` lets any side effect in, so it gives no
  reasoning benefit; most tagless-final type classes have no laws; use a
  concrete effect type, code to interfaces, and minimize effectful code.

## Existing skills

- **[VirtusLab]** VirtusLab, `scala-skill`, skill `direct-style-scala`,
  <https://github.com/VirtusLab/scala-skill>, commit `2b4d8d0` (16 October
  2026). *Read.* Licence: Apache-2.0, as declared in its `plugin.json`. Rules
  adapted from its "Coding style" and "Functional programming" sections and
  from the chapters "Code organization and visibility", "Domain modeling" and
  "Error handling": one concern per function; explicit return types on public
  members; narrowest visibility, and `private[root]` treated as wide; no
  class-level `var`; immutable collections; lawful APIs (clock, randomness and
  ids passed in); opaque types for domain values; enums instead of `Boolean`
  parameters; `Either` smart constructors; typed error hierarchies;
  recoverable versus unrecoverable failures; concept-named packages, with
  `Types.scala` and `Models.scala` as smells; split packages as they grow;
  targeted tests; zero warnings with `-Wunused:all`, `-Wvalue-discard` and
  `-Wnonunit-statement`. Its Ox, Tapir and direct-style material does not apply
  to FrFlow, which uses cats-effect and http4s. The rules above are rewritten
  for cats-effect (`IO` at the edges, `Resource`, `Ref`).
- **antigravity** `skills/super-code/scala` and `skills/scala-pro` (MIT).
  *Read.* Nothing was adopted beyond the common advice against `.head`, `.get`
  and `filter(...).head`, which F3 covers through King.
- **[Owner]** `docs/USAGE.md` in this repository: "One type to a file, in a
  package per concept".

### Notice for adapted material

Portions of `SKILL.md` and `rules.md` (the rules marked [VirtusLab]) are
adapted from VirtusLab `scala-skill`, licensed under the Apache License,
Version 2.0 (<https://www.apache.org/licenses/LICENSE-2.0>). They were
modified: rewritten for cats-effect and this repository, with new examples.
No text from that project is copied verbatim.

## Where the sources disagree

### Tagless final or concrete `IO` (E8)

- Volpe builds the application in tagless final, with algebras over `F[_]` and
  capability type classes. The cats-effect tutorial writes polymorphic
  `F[_]: Sync` code and uses `IO` only in `run`.
- De Goes argues that for applications this is premature indirection: `Sync`
  admits any side effect, the type classes mostly lack laws, and testability
  comes from coding to interfaces, which works without tagless final. He
  recommends a concrete effect type.
- Odersky's Lean Scala prefers direct style to monadic effects.

**Rule:** application modules (`check`, `ledger`, `api`, `cli`, `web`,
`agent`) use concrete `IO`. The core has no effect type at all. `F[_]` stays
only where FrFlow has an abstraction with two or more interpreters in use and
laws: user flows, run over state models and over real boundaries
(`Flows.run[F]`). **Reason:** FrFlow is an application and a DSL. It is
not a library offered to users of several effect systems. It has one effect type, and
the testability that tagless final promises comes here from a pure core and
in-memory fakes of interfaces.

### Direct style or monadic effects

Odersky recommends direct style, while Typelevel's ecosystem is monadic.
**Rule:** FrFlow stays on cats-effect, since changing effect systems is out of
scope. Keeping `IO` to the edges (E1, E2) keeps the monadic code small, which
answers most of Odersky's concern.

### `require` (F8)

Effective Scala uses `require` for API contracts. VirtusLab forbids `require`
for anything recoverable and uses `Either`. King says to make the check
unnecessary by construction. **Rule:** types first. `require` and `assert` are
for invariants whose failure is a bug in FrFlow. A mistake by the developer in
their model is a value: a compile error through the types where possible,
otherwise a validation error naming the node, collected with the others.
**Reason:** the developer can act on a model error, and an exception from a
builder in a `val` initializer reports only the first one.

### Files (M3)

The style guide names a file after its class "or, if it has more than one
class, the parent class". VirtusLab bundles a sealed hierarchy, a service and
the types only it builds, or a trait and its single implementation, in one
file. The owner's rule is one type to a file. **Rule:** the owner's, with
`enum` preferred so a family of cases is one type. A sealed trait's cases must
share its file (a language rule) and count as one type.

### Default arguments (F6)

Li Haoyi places default arguments low on his ladder of dependency-injection
techniques: simple and often enough. VirtusLab and Effective Scala pass
dependencies explicitly. **Rule:** defaults are allowed for optional settings
on published DSL and CLI entry points. They are not allowed for collaborators
or effects, or on domain fields. **Reason:** `report: Violation => Unit =
Violation.log` on an internal function hides a side effect from every caller.

### Embedded DSLs (S1 to S4)

Odersky's Lean Scala prefers the core language to embedded DSLs. FrFlow's
product is a DSL. **Rule:** keep the DSL, with a minimal surface (few entry
points, each building one case), plain Scala inside, and inline and macros only
for source capture.

### Wrapping primitives (D4)

VirtusLab says never to use a raw primitive for a domain value. Li Haoyi's
practical type safety wraps where it prevents real mistakes, and his least
power argues against ceremony. **Rule:** wrap when two values of the same
primitive type could be confused (ids, hashes, paths) or the value has an
invariant (a relative path inside the project, a sample rate of at least 1).
Prose in the developer's words (`statement`, `why`) stays `String`.

### Implicit conversions (T3)

The Scala 3 reference and Odersky discourage them. FrFlow lifts literals into
`Term` with conversions, so that models read as formulas. **Rule:** allowed
for literal lifting only, all in one place. A conversion that hides an
access or a computation is a finding.

### Braces

VirtusLab requires braceless syntax. The style guide predates Scala 3 and
shows braces. **Rule:** braceless, as the repository is written. Braces are
fine for a one-line partial function (`{ case ... }`).
