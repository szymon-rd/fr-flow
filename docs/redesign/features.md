# Feature audit

Every user-visible feature and DSL operation of today's library: its concept in the rebuild, where the examples use
it, and what the rebuild does with it. Section numbers are those of `ARCHITECTURE.md`; "owner §n" is a section of
`owner-decisions.md`. Section 8 of `ARCHITECTURE.md` summarises what is removed, and section 9 says when each example
is ported.

The use column counts occurrences in `examples/*/src`, as auth / keycloak / crm / sharing (rooms is named where it
adds a use), measured with grep on 3aa8cd7 and checked on e0fa3d9. "Tests only" means only FrFlow's own suites use it;
"—" means not counted. Explanations are the numbered notes under each table.

## The DSL: vocabulary and terms

| Feature | In the rebuild | Use | Rebuild |
|---|---|---|---|
| `Opaque(name, means)`, `User.T` | `vocab.Sort` | all | change, note 1 |
| `Param[T](name, means)` | `Declaration`, `Definition` | all | change, note 2 |
| `Param` without a Lean type (code-only) | a Definition with no `LeanType` | crm, sharing | keep, note 3 |
| `define { … }` (0 to 6 inputs), `program { … }` | a `Definition` carrying its meaning | 0 / 18 / 30 / 58 | change, note 4 |
| `object X extends Data[X]` | `derives LeanType`, once per type | 1 / 4 / 13 / 23 | change, note 5 |
| `b.start` (a record's field) | `Records.field` by a derived `Selector` | all | keep |
| `==` on terms refused with a message | `Term.NoEquality` | — | keep, today's message |
| `LeanType.product[T]`, `LeanType.sum[T]` | the same derivation, without the constructor | sharing 8 + 5 | keep |
| the Boolean and equality operators | `Logic`, `Equality` | all | keep, note 6 |
| `==>` | `Logic.implies` | all | change, note 7 |
| `True`, `False` | `Logic.bool` | — | keep, note 8 |
| `forall`, `exists` | `Quantifiers` | 4+2 / 14+2 / 17 / 37 | keep, note 9 |
| `always[T](x => …)`, `always(stored)(s => …)` | `Quantifiers.always`, `Range` | rooms 2 | new, note 10 |
| `.on[Case]` match, `.on(X.Case)` | `Sums.cases`, a derived eliminator | 0 / 12 / 29 / 98 | keep, note 11 |
| `c.fold(a, b)`, `o.fold(z)(f)`, an `Either`'s fold | `Logic.cond`, `foldOption`, `foldEither` | 0 / 9 / 8 / 73 | change, note 12 |
| `xs.foldLeft(z)((acc, x) => …)` | `Lists.foldLeft` | not counted, note 13 | keep |
| `let(v)(x => …)` | `Functions.let` | sharing 5 | keep |
| `make[R](fields…)`, `x.updated(_.field, v)` | `Records.construct`, `Records.copy` | not counted, note 14 | keep |
| list, option, map, set operations | the `Lists`, `Options` algebras | all | keep, note 15 |
| `xs.allDistinct`, `xs.pairwise(r)`, `xs.forall(d)` | `Lists.nodup`, `Lists.pairwise` | rooms 3 | keep, note 16 |
| a project's own operation (`count`) | a define, or an algebra outside the core | — | keep, note 17 |
| `BigInt` arithmetic; `Int`/`Long` compare only | `NumKind` | all | keep |
| `p.value` in plain code | `env(d)` | 34 | change, note 18 |
| `d.fn` in plain code | `d.fn(env)` | 8 (main) | change, note 19 |

1. `Opaque(means)` takes its name from its val.
2. A value only statements speak of is a `Declaration[A](means)` (auth's `access`, `authorized`, `signedIn`), applied
   only under `Stating`, so code using one does not compile. A value code uses is a `Definition[A](means)`, given its
   meaning once (`implementProven`, `implementTested`, `implementValue`, `implementProvided`). Each is of any type and
   named from its val; validation reports `Undefined` and `DeclarationInCode` (2.2; `FormsSuite`, `AuthSuite`).
3. It is the same word, `Definition[A](means)`, over a type with no `LeanType` (an overload taking
   `NotGiven[LeanType[A]]`): a code-only symbol, provided where the code runs (crm's and sharing's connections) and read
   only through `env(d)` in plain code. A statement mentioning one is `Problem.CodeOnlyInStatement`.
4. `val covers = define { … }` is a `Definition[(Booking, BigInt) => Boolean]` carrying its proven code, its written
   lambda and its `core.term.Body` (a `lam` per input). It is named as its val at compile time, called by
   `Definition.apply`, passed as a function, printed once as its Lean `def` and run by the evaluator. A meaning is
   given once (`Fault.MeantWhereWritten`) (2.2).
5. Each domain type adds `derives LeanType` (`DataMacros`); `Data[X]` keeps only the constructor on terms
   (`Claims(r, u, rs)`). A derivation at every use would pass the JVM's size limits on sharing's largest file (10.1).
   Forgetting it says "X is not a domain type yet: add derives LeanType to its declaration".
6. The operators are `===`, `=!=`, `&&`, `||` and `!`, each an `Expr.Prim` in the IR.
7. `implies` is alphanumeric, so it binds last: `a && b implies c` is `(a && b) implies c`. `==>` is deleted, since
   its precedence (that of `=`) bound tighter than `&&` and `||`. A chain `a implies b implies c`, which Scala groups
   to the left, does not compile unless its grouping is written in parentheses (4.2).
8. A Scala `Boolean` is not made a term implicitly.
9. The body is a host function, its variable named by each interpreter where it binds it; the user never sees an
   interpreter (4.2). There is no `exists` word (owner §15): today's `exists t` is written `!forall(t => !…)`, which
   is logically the same; a list's `.exists` stays, a list operation.
10. Every value of `T` that can be made, and every state the store reaches: a hypothesis everywhere (`Guarded`), kept
    by every writer (`cover_<op>`), met at the start (`start_<node>`), shown to admit a value (`inhabited_<node>`)
    (2.3; `AlwaysSuite`).
11. The eliminator is derived per type from `Mirror.SumOf` (`CaseMacros`); each arm is a host function over the case's
    fields (`When`), the case found by a derived test, with no cast; `Expr.Match` in the IR (`ChangesSuite`). An arm is
    named by its case's type, `.on[Change.Book](b => …)`, and a case without fields by its singleton type,
    `.on[Change.Clear.type](…)`, in any position: the only spelling.
12. A Boolean's fold is `when(c)(a).otherwise(b)` (`Conditional`), since a `fold` hid which branch is which; an
    option's and an either's folds stay (`ChangesSuite`, `BookSuite`). In the IR: `Expr.If`, `Expr.Match`.
13. `foldLeft` appears in crm, keycloak and sharing, in Scala as well as in terms. It has two host-function variables;
    `Expr.Fold` in the IR (`ChangesSuite`).
14. Records are made in terms through today's constructors. `construct` is a derived curried `Constructor`; `copy`
    goes by the field's `Selector`, its setter Scala's `copy`; `Expr.Make`, `Expr.Copy` in the IR (`ChangesSuite`).
15. The algebras grow to today's set (`PrimOp`, `Iterate`, `Fold` in the IR).
16. The owner's list relations (owner §4): printed `(List.Nodup xs)` and as Lean's `List.Pairwise` over a
    two-variable lambda. A define is a function of terms, so `forall` takes one (`RoomsSuite`, the term generator).
17. An outside algebra has its meaning in the core and, optionally, interpreters that know it (`Count`, 4.2).
18. No ambient state (owner §2, B): every use is rewritten when its example is ported.
19. The define's term is run by the evaluator, curried, and nothing is compiled; the values are passed explicitly.

## The DSL: nodes

| Feature | In the rebuild | Use | Rebuild |
|---|---|---|---|
| `Node.claim`, `.contract`, `.assumption`, `.invariant`, `.definition`, `.design` | `Statement`: `Claim`, `Assumption`, `Design` | all | change, note 1 |
| `Node.invariant[A, B](…)(rule)`; ideas glued with `&&` | a claim of `always` | crm 1, keycloak 1; rooms | change, note 2 |
| `Node.contract(op)((a, b, result) => …)` | a claim read as a call | all | change, note 3 |
| a flow contract's lambda `(input, result, before, after) => …` | a claim read as a run | crm 1, sharing 3 | change, note 4 |
| `why = "…"` on every node | the signed decision's reason | 10 / 23 / 26 / 58 (rooms 2) | remove, note 5 |
| `idea = "Section"`, `FrModel(…, idea = …)` | none | 77, all four | remove (owner §1) |
| `Node.assumption(store)(Stored)(statement)` | a model and `store.behavesAs(stored)` | crm, sharing, rooms | change, note 6 |
| `stored.initially`, `writtenOnlyBy`, `changedOneRunAtATime` | `OutsideFact`, said by assumptions | rooms 3 | new, note 7 |
| `book.calledOnlyWith(request => …)` | a type for what comes from outside, `always` assumed on it | rooms 1 | change, note 21 |
| `Boundary[B]("store", means)` | `BoundarySig`, `BoundaryOps[B]`, `Boundary.failing[B, E]` | crm, sharing, rooms | change, note 8 |
| `.under(parents*)`, `.replaces(other)` | `Edge.PartOf`, `Edge.Replaces` | all; `.replaces` none | change, note 9 |
| `.assuming(premise*)` | `Edge.Assumes` | rooms | new, note 10 |
| `.keeps(invariant)(view)`, `.exempt(invariant, because)` | none | keycloak, crm | remove, note 11 |
| two definitions of one term as alternatives | none | none | remove, note 12 |
| `Node.definition(…)(authorized := …)` | a claim of one equation, or a `define` | auth 3, crm, sharing | change, note 13 |
| `.examples(bindings*)(expect/reject…)` | examples as tests beside the model | 1 / 4 / 10 / 29 | change, note 14 |
| `bind`, `bindTable` | `example.Given`: `d := value` | bind all; bindTable auth 1 | change, note 15 |
| `.expects(statement)(consequence)` | a claim the expecting claim refines | crm 4 | change, note 16 |
| `.checkedBy(check)` | none | keycloak 1, crm 4 | remove, note 17 |
| `.checkedAtRunTime(RunCheck)` | none | tests only | remove (owner §2) |
| `.leftOpenAbove` | `Claim.reliance = LeftOpen` | sharing 5 | keep, note 18 |
| `.failsChangingNothing[E]`, `.onFailure[E]` | the run's failure clause | sharing 2 / 1 | change, note 19 |
| `.checkedAgainst(start, read)`, `.implementedBy(start, read)` | `AdapterCheck`, `ModelTests.run` | crm 1+2, sharing 1+3 | change, note 20 |

1. Three forms only, `Node.claim(statement)(formula)`, `Node.assumption(statement)(formula)` and
   `Node.design(statement)(paths*)`, without `why` and without an id (the id is the val's name as written).
   `Node.contract`, `Node.invariant` and `Node.definition` are removed and said as the rows below say; how each claim
   is checked is derived and shown (2.1, 2.7; `FormsSuite`, `CheckingSuite`).
2. What always holds is its own claim of `always` (owner §10, §13, §15): a hypothesis on every value in Lean,
   checked where a tested Definition makes a value, met by generated values, kept by every program writing the store.
   Today's relation of answers (crm's `noCrossTenantRead`, keycloak's `realmIsolation`) becomes a claim `forall` over
   the Definitions it relates. Gluing ideas with `&&` is a style guide, never checked (2.3; `AlwaysSuite`).
3. `Node.claim(statement)(forall((a, b) => op(a, b) === …))`. The call reading (`CallForms`, its post by `Opened`)
   is derived, never a kind; a claim reading as no call is checked as a whole; another Definition on the same inputs
   is an ordinary mention (2.7; `FormsSuite`, `CrmClaimsSuite`).
4. `forall((now, before) => runExpiry(now).from(before) { (result, after) => … })`, a model's state read as
   `databaseModel.in(before)`. The post is over today's four inputs, so crm's Lean prints byte for byte (`ExpiryJob`).
5. `show` and review show the reason from the ledger (`Says.reason`); the texts go into each example's first
   decisions' reasons when the owner decides them (owner §2).
6. The model is an instance of the tagless trait over its state,
   `final class Stored[F[_]: Flow](state: Model[F, S]) extends Bookings[F, Term]`, declared with its boundary as
   `val stored = store.model(means)(Stored(_))` and assumed by `Node.assumption(statement)(store.behavesAs(stored))`
   (owner §16). It is a premise of every check of code calling the store, written `.assuming(storeModel)`, never a
   part; Lean prints it in the `Boundaries` module (`LowerModels`), and Scala runs it through `World.models` (2.6,
   3.2).
7. The facts the rules about `always` rest on: the start, the only writers, one run at a time (owner §16, §17). Each
   is said by an assumption, reviewed as any node, and listed by each claim resting on it; `Premises` checks the lists
   (`PremiseMissing`, `PremiseNotNeeded`, `WriterNotListed`). Atomicity is assumed, asynchrony future work; `show`
   lists each fact a check rests on (2.6; `BookSuite`, `CheckingSuite`).
8. `Boundary[B](means)`, named from its val, over `trait B[F[_], T[_]] derives BoundaryOps`. A boundary whose calls can
   fail is `Boundary.failing[B, E](means)`, today's form, setting `BoundarySig.failsWith`.
9. `.refines(parents*)` replaces `.under`; `.replaces` is kept.
10. A premise the node's proof assumes, an assumption or a claim of `always`, never a part (`PremiseNotAssumed`,
    `OutsideAsPart`, `OutsideClaimed`). It is the one mechanism for a premise, the outside's included, and its list is
    checked against what the check rests on (2.4, 2.6).
11. Who keeps an `always` is derived (`Scope`), and a claim mentions only what it constrains, so nothing is exempt; a
    relation of answers is a claim over the Definitions it relates (owner §15).
12. A Definition has one meaning; alternatives are two claims, one `.replaces` the other (owner §15).
13. The equation is also the Declaration's consistency witness (`AuthSuite`); a value fixed in the model is
    `implementValue(d)(v)` (2.8).
14. Examples leave the nodes (owner §18): `class GrantedExamples extends FrFlowExamples(rooms)` with
    `example("back to back: granted"): granted(…) is true`. Each is checked against the code and, in Lean, against
    the claims (`example_<i>`); one setting provided values is "checked in Scala only"; nothing depends on them.
    `allows`/`forbids`, `Call` and the rule that a contract has a `forbids` are removed (2.10; `ExamplesSuite`,
    `ExampleRunSuite`).
15. `d := value` in an example, `d` a provided Definition; a table is a value of its type.
16. The consequence is its own claim, refined by the expecting one, so `complete` proves it from its parts; `expect_i`
    goes. An expectation over literal values (a fixed scenario) is an example, not a claim (owner §18):
    `example("…"): (… implies …) is true`, checked against the claims in Lean (`example_<i>`).
17. A cheaper check meant for run time (owner §2); its Lean obligation `check` (post implies check) goes with it (8).
18. On a claim only; on an assumption it is `Fault.NotAClaim`.
19. `.failsChangingNothing[E]` sits on the run in the formula (`Ran`). `.onFailure` becomes the failing side of the
    claim's own run, one formula for both outcomes:
    `handle(r).from(before) { (answer, after) => … }.failing { (error: Term[E], after) => … }`
    (`SharingClaimsSuite`).
20. On the model, with named arguments: `stored.checkedAgainst(start = held => …, observe = adapter => …)`. Runs are
    generated from the boundary's signature (`Runs`), answers then states compared (`CodeTable.realized`). It is the
    only check of an outside system's adapter (3.7; `StoreModelSuite`). The project's own implementation is checked with
    `stored.implementedBy(start, observe)`, as today. An outside system's is run at most 200 times, the project's own on
    every case (1,000), and a node's count is the sum of its checks'.
21. Statements are about values only (owner §21): nothing is assumed of a function's inputs. What comes from outside
    gets a type of its own, rooms' `Request`, and what is trusted about it is an assumption of `always` on that type:
    `fromTheForm`, "The booking form sends only requests that end after they start", is
    `always[Request](r => r.start < r.end)`. `book` takes a `Request`; `asBooking` makes the `Booking` stored, and
    `endsAfterStart`, a claim on `Booking`, is proven of it (`cover_book`). The assumption is trusted only for what
    no covered code makes. Each check whose Lean form carries its guard lists it, rooms' two roots included; one that
    does not is refused, naming it (`PremiseMissing`), as is a claim of `always[T]` needing `T`s from outside that no
    assumption speaks of; one listing such an assumption it does not need, `PremiseNotNeeded` (2.6; `BookSuite`).

## The DSL: code

| Feature | In the rebuild | Use | Rebuild |
|---|---|---|---|
| `kb.implement(c, calls*)(code)` | `Code.Tested` | 3 / 2 / 3 / 1 (rooms 1) | change, note 1 |
| `kb.implementProven(c)(define)`, `(define, runs)` | `Code.Proven` | keycloak, crm, sharing | change, note 2 |
| `kb.implementValue(d)(v)`, `kb.implementProvided(d*)` | `Code.Valued`, `Code.Provided` | auth | new, note 3 |
| `kb.implementProven(job)(flow)` | `Code.ProvenFlow`: a recorded program | crm, sharing, rooms | change, note 4 |
| `kb.service(c)(bindings*)` | `knowledge.code(d)(bindings*)` | 2 / 4 / 10 / 22 | change, note 5 |
| `kb.run[F](contract)(bound*)` | the program called directly | crm 2, sharing 3 | change, note 6 |
| `kb.reporting(v => …)`, `Violation`, `ContractViolation` | none | crm, keycloak servers; suites | remove (owner §2) |
| `kb.generating(gen)`, `Gen.derived`, `.describedAs` | `example.Gen` (data) and `testing.Draw` | crm 1, sharing 12 (rooms 2) | keep |
| `kb.testedWith(TestSettings)` | `testing.Settings` from `project.Config` | tests only | change, note 7 |
| `FRFLOW_SEED=fresh` | `project.Config` | CI doc | keep |

1. `implementTested(d, calls*)(env => code)` on a Definition, the code built from the values it is given (owner §2,
   B; §15); it is tested against every claim mentioning `d`.
2. `implementProven(d)(define)` on a Definition; runs beside a define are a tested Definition of their own.
3. A value fixed in the model, substituted in Lean; or a value given where the code runs, bound by an example, drawn
   by a test, passed in production, with every claim stated for every such value (owner §15; 2.2). Auth provides
   `grants` and `sessions`.
4. `implementProven(book)(bookIfGranted)` on the Definition; the program is tagless (owner §2, C), and `impl` is
   asked of its run on the models (`f_run`) for each claim mentioning it.
5. The same wiring (`eval.run.Wiring`) with no check (owner §2); servers call the code directly and lose their
   `ContractViolation` branches (8).
6. Production runs the program in `IO` over `eval.Running`, reached through `knowledge.running`, with each adapter
   lifted, `database.lifted(adapter, running)` (owner §2, C; 4.4).
7. It moves to the checker's configuration.

## Programs over boundaries

| Feature | In the rebuild | Use | Rebuild |
|---|---|---|---|
| `trait Database { def load: Flow[CrmStore] }`, `Boundary[T]` | `trait Database[F[_], T[_]]`, `BoundaryOps` | crm 1, sharing 1+2 | change, note 1 |
| a program as a `Flow[A]` value | a class over `F[_]: Flow` | crm, sharing | change, note 2 |
| implementations returning `Flow.effect(x)(f)` | adapters over plain values, `Database[IO, Id]` | crm 9, sharing 5 | change, note 3 |
| `StateModel[S]`, `state.get/set/update` | the boundary's trait over `Model[F, S]` | crm 1, sharing 2 | change, note 4 |
| `for`, `flatMap`, `map`, `pure`, `*>`, `as`, `void`, `<*`, `flatTap`, `tupled`, `sequence` | cats syntax on any `F[_]: Flow` | crm, sharing | keep, note 5 |
| `traverse_`, `traverse`, `foldM` | `Flow.each`, `collect`, `fold` | crm, sharing | keep, note 6 |
| `c.foldF`, `whenA`, `unlessA` | `Flow.cond` (`Prog.Branch`) | whenA sharing 3 | keep |
| `ifM` | `Flow.ifM` | tests only | keep, note 7 |
| `raiseError`, `handleErrorWith`, `attempt`, `retry(Schedule)` | `Flow.raise`, `handle`, `attempt`, `retry` | sharing 7 + 1 | keep, note 8 |
| `guarantee`, `bracket` | `Flow.guarantee` (`Prog.Guard`), `bracket` | tests only | keep, note 7 |
| `timeout(seconds)` | `Flow.timeout(clock)` | tests only | keep, note 9 |
| `parTupled` | `Flow.parTupled` (`Prog.Par`, `commute_i`) | tests only | keep, note 7 |
| `parTraverse`, `parTraverseN` | `Flow.parCollect`, `parCollectN` (`Prog.ParEach`, `commute_i`) | sharing 3 | keep, note 6 |
| `race` and the `Races` boundary | `Flow.race` (`Prog.Race`) | tests only | keep, note 10 |
| `atomically` | `Flow.atomically` (`Prog.Atomic`) | sharing 5 | keep, note 11 |
| `Flow.now`, `sleep`, `waitUntil`, `Clock`, `ClockModel`, `FakeClock`, `SystemClock` | `Clock[F, T]` with its model | sharing | keep, note 12 |
| `Flow.every(period)(job)` | a scheduler over a program | sharing 2 | keep |
| `FaultPlan`, `World(…)`, `Failed(…)` in examples | values in an example's fact | crm 10, sharing 3+8 | change, note 13 |

1. `def load: F[T[CrmStore]]`, `Boundary[Database](means)`. `BoundaryOps` is derived: the signatures, a recording
   instance, a by-name caller for tests, a lifted adapter, the model read. The examples' boundaries are rewritten
   (owner §2, C; 4.4).
2. `final class Job[F[_]: Flow](db: Database[F, Term])`: its values are `Term`s and its effect is abstract;
   `program { (a: Term[A]) => Job(database.recording).run(a) }` records it for Lean (owner §2, C).
3. `database.lifted(adapter, running)` gives programs their `Database[IO, Term]`; `Flow.effect` goes.
4. A model is an instance of the boundary trait over its state (`Model.recorded`), read into `vocab.StateModel`: the
   same meaning in another form.
5. From cats, not FrFlow's own; `Prog.Bind`, `Pure`, `Let` in the IR.
6. `each` is written, with its element's `LeanType`, and recorded (`RecordingSuite`). `collect`, `fold` and `parCollect`
   are added in step 2 (`Prog.Loop`, `Collect`, `Accumulate`, `ParEach`), each with a `RecordingSuite` test (4.4).
   `parCollectN(n)` keeps `parTraverseN`'s limit, recorded as `Prog.ParEach(…, Some(n))`.
7. Kept by the owner's decision (owner §2), recorded as the step Lean reads with a test in `RecordingSuite`, and
   given a use in an example: `ifM` in crm (step 12); `guarantee`, `bracket` and `parTupled` in sharing (step 13).
8. `raise` and `handle` are written in `Recording` and `Running` and tested; `attempt` is added in step 2.
   `retry(clock, waits)` is kept (owner §2), built from `handle` and the clock's `sleep` as today, a fold of the waits;
   sharing's `Delivery` uses it (step 13).
9. The clock is read around the program, nothing cancelled, as today; kept by the owner, tested, used in sharing (step
   13).
10. Read as the scheduler's choice; kept by the owner, tested, used in sharing (step 13).
11. A `Mutex` in production.
12. `Clock[F, T]` is FrFlow's own boundary with its model; `FakeClock` is an instance for tests.
13. Written in the example's fact (a world made, a run's outcome stated); `RunExample` and `RunEnd` go.

## Checks Lean makes

| Obligation | In the rebuild | Use | Rebuild |
|---|---|---|---|
| `complete`, `holds`, `root_impl`, `impl` | `Prop.Implies` over `ClaimOf` | — | keep, note 1 |
| the root: a claim or invariant without parents | `Refinement.roots` | — | change, note 2 |
| `needed_C`, `vacuous`, `restates`, `clash`, `unsat` (tries) | `TryKind` | — | keep |
| `restates_i_C`, `idle`, `feasible`, `cover_X` | as today | — | keep, note 3 |
| `expect_i` | none | crm 4 | remove, with `.expects` |
| `start_<node>`, `made_<maker>`, `inhabited_<node>` | `Prop.Starts`, `Prop.Makes`, `Prop.Inhabited` | — | new, note 4 |
| `consistent_<i>` | `Prop.ForEvery`, `Prop.ForSome` (`Joint`) | — | new, note 5 |
| `satisfiable_<i>_<node>` | `Vacuity.Satisfiable` (`Conditions`, `Possible`) | — | new, note 6 |
| `example_<i>` | `proof.whole.ExampleGoals`, a try | — | new, note 7 |
| `check` (post implies `checkedBy`) | none | keycloak 1, crm 4 | remove, with `.checkedBy` |
| `eval_i`, `probe_j` (Lean against Scala) | none | — | remove, note 8 |
| `commute_i` | `Prop.Commutes` | — | keep, for `parTupled` and `parCollect` |
| a failed step refuted by a case Lean proves | `StepRefutation`, `RefutesModule` | — | keep |
| the contradiction search (`unsat`, `clash`) | `TryKind` | — | keep, note 9 |
| authored proofs, `scaffold`, proof rules | `Discharge.Authored`, `proof.reading` | — | keep |

1. `impl` is the step of a node with proven code from its stated parts, the code put in, or a leaf's `reliesOn`, a proof
   that goes round refused (`RestsOnItself`); `complete` is not asked of it (rooms' root, `BookSuite`; 2.7).
2. Several root statements, the claims without parents, on any Definitions and Declarations, a statement relating them
   included; no `SeveralRoots` problem, and keeping them a concise few is the author's. A service's purpose about its
   entry program is one: rooms' `bookWhenFree` and `answersWhetherBooked`, beside its claims of `always` (owner §9,
   §11; 2.5).
3. `cover_<op>` is asked of each program writing a store, for each `always` about it (2.3).
4. Every state a store may start in (`initially`) meets what always holds of it; every result of a proven define or a
   store operation on its model meets each `always[T]` its guard applies to (rooms' two `made_inRoom`, proven); each
   `always[T]` admits a value, its witness found by the search (owner §13, §18; 2.3, 2.9).
5. The bottom statements and the assumptions beside them, grouped by shared open values, jointly satisfiable for every
   value provided, discharged by their witnesses (`LowerWitness`, `frflow_witness`); witnesses come from equations,
   bounds and proven code, and a group without one is "consistency not proven", a status of its own (owner §18; 2.8;
   `ConsistencySuite`, `AuthSuite`).
6. Each condition `A` of `A implies B` can hold: a witness from the search, else stated only, "not shown" (owner §18;
   2.9; `VacuitySuite`).
7. Each example follows from the claims constraining what it mentions; nothing depends on it (owner §18; 2.10).
8. Examples are checked against the claims in Lean and against the code in Scala, separately (owner §18);
   `Prop.Evaluates` and `LeanAndScalaDisagree` go.
9. An early refuter only: consistency is never inferred from it (owner §18; 2.8).

## Tests

| Feature | In the rebuild | Use | Rebuild |
|---|---|---|---|
| property tests of plain code against its contract | `PropertyTests` over `CallCheck` and `Wiring` | — | keep, note 1 |
| an outside system's adapter against its promise | `PropertyTests` and the examples | crm, keycloak | keep, note 2 |
| model tests of `implementedBy` and `checkedAgainst` | `ModelTests.run` of an `AdapterCheck` | — | keep, note 3 |
| fault sweep, interleavings | `Interleavings[F[_]: Async: Random]` | sharing | keep, note 4 |
| the step-refutation search | `testing.search.StepRefutation` | — | keep |
| the witness search | `testing.search.Witnesses`, `Small` | — | new, note 5 |
| a contract changed under unchanged code | `decision.review.Cause.movedUnderCode` | — | keep, said of the claim |

1. Derived generators seeded by the examples, shrinking, coverage of a claim's parts, counterexamples saved and
   replayed, and the `.frflow/tests.json` cache. Each case draws the inputs, makes the values the code reads with
   `Wiring`, calls through `Fn` and is judged by `CallCheck`, against every claim mentioning the tested Definition: per
   call where the claim reads as one, else the claim evaluated whole on its drawn variables. A claim with no Scala value
   is "not checked" (`Outcome.NotChecked`, shown as `Warning.NotChecked`), never a failure, and nothing is shrunk, saved
   or replayed for it. Coverage counts what each case reaches: each implication's premise holding, each side of an `or`,
   each condition both ways, each arm of a match, each list or option a quantifier ranges over not empty; in model tests
   each operation called and each branch of the model's steps. `cases` is the number tried, a case that cannot be drawn
   not tried and the shortfall said. `PropertyTests.of` is written (`CalendarSuite`: the README's calendar on 500
   cases); shrinking is step 5's, the cache step 8's. What the running service checked on each call is checked here,
   before production (4.9).
2. crm's `recordsByQuery` and keycloak's `sessionLookup`, tested against their assumptions' formulas; this replaces
   the run-time check of every adapter call (8).
3. Over two `World`s: the adapter, by `BoundaryOps.call`, and the model, by `World.models`; runs generated by `Runs`
   through `Respecting` (`StoreModelSuite`: rooms' store against its model).
4. Over the recorded program, run on the adapters.
5. SmallCheck-style small values after the generators' own, at most 5,000 candidates, each judged by the evaluator:
   the witnesses of vacuity, given to Lean (owner §18; 2.9).

## Run time

| Feature | In the rebuild | Use | Rebuild |
|---|---|---|---|
| the `runtime` module | none | crm, keycloak servers | remove, note 1 |
| facts about a service's values, checked when wired and on change | trusted, as every assumption | sharing | change, note 2 |

1. "FrFlow is for testing before production and strict static guarantees" (owner §2). The module held `service`
   wrapping code to check each call (`enforce`, `Service`, `Guard`), sampling (`RunCheck`, `checkedAtRunTime`), the
   assumption watch, the violation reporter and `ContractViolation`; section 8 says what this removes and what moves
   to tests.
2. Sharing's `HousekeepingOnTime`: checked under the examples' `:=` values and the tests' values only.

## Decisions and review

| Feature | In the rebuild | Use | Rebuild |
|---|---|---|---|
| accept, reject, confirm, revisit, gone; `-m`, `--yes`, `--revisit` | `rules.Decide`, one rule per command | — | keep |
| causes, rewording, the mechanical batch, refusals | `review.*`, `rules.*` | — | keep |
| signed decisions; keys filed in `.frflow/keys/<name>.pub` | the deciders' list, `.frflow/deciders` | — | change, note 1 |
| the ledger file | `wire`'s codec of `Ledger`, the new payload | — | change, note 2 |
| content forms `V1`/`V2`, `confirm --rebind`, `Retired`, `Text` fingerprints | none | — | remove, note 2 |
| the code cause from governed files | `CodeFingerprint` by the simple lexer | — | change, note 3 |
| held aside by a layer | `Views.inbox(aside)` | — | keep |

1. A committed, developer-signed list of who may decide (owner §2): a decision counts only when its key is listed
   under its decider's name; each version of the list is signed by a key the version before it listed; FrFlow reads
   the committed versions only, so filing a new key under a new name decides nothing (6).
2. The ledgers start fresh (owner §2, G): a new format, and old ledgers are not read.
3. Comments stripped, lines and indentation kept (owner §2, F; 6).

## Front ends

| Feature | In the rebuild | Use | Rebuild |
|---|---|---|---|
| the CLI's commands and flags | `cli` over `Reading`, `Deciding`, `Proving` | — | keep, note 1 |
| the web view | `web` over the same algebras | — | keep |
| `CliExtension`, `WebExtension` | `api.Extension` | — | keep |
| `frflowInit`, `frflowInitAgent` | `cli.Init`, `agent.Init` | — | keep, note 2 |
| the agent layer | `agent` over `api` | — | keep, note 3 |
| `bench/`, `examples/scale` | tooling | — | keep, rebuilt last |
| `.frflow/kb.json` | `wire.snapshot` rows, made by `Rows` | — | keep, note 4 |

1. `tree`, `show [--full]`, `diff`, `inbox`, `find`, `review`, `render`, `check [NODE]`, `scaffold`, `status`, `ci`,
   `--plain` and the exit codes; `--json` on `status` and `check` now prints the snapshot (4). New: `rebase` (the owner
   accepts the ledger as it reads now as where its committed history starts: after a merge, an unreadable committed
   ledger or a deletion he accepts; refused unless his key is listed), `deciders` (the first deciders' list, signed by
   the developer's key) and `export` (the snapshot written and printed). `show` and review give the reason from the
   decision, and `show` how each claim is checked (`Says.checking`); `status` shows the consistency groups and the
   examples (`WholeView`, `Warning.ConsistencyNotProven`).
2. `init` also writes `.frflow/deciders`, signed by the developer's key.
3. Its proposals carry their rationale in the request or the conversation, not in the node; questions have no numbers.
   It never decides: its commands and routes read the view and ask, which its `ArchitectureSuite` checks on the compiled
   classes.
4. Every fact is kept, regrouped by kind, with the consistency groups (`GroupRow`) and the examples (`ExampleRow`).
5. Dropped from today's front ends, each with its reason: IDEA.md and every case about it (owner §1: the idea is told
   in chat, and the root statements come first); rename detection of a gone node (the view carries no rename: a
   renamed val is a gone node and a new one, 10.1); the agent's "move what rests on a rejected node" (a rejection
   already sends the nodes below back, so they are the agent's to replace).

## Summary

Removed: the `runtime` module and everything only it used (`service`'s checks, `checkedBy` and its `check` obligation,
`checkedAtRunTime`/`RunCheck`, sampling, the assumption watch, the reporter, `ContractViolation`); `why` on nodes; the
ambient scopes (`Param.value`, the fresh-variable counter) and any numbering of variables before an interpreter binds
them; today's `Flow` values and `Flow.effect`; content forms, `confirm --rebind`, `Retired`, `Text` fingerprints and
filed keys as authority; `Node.contract`, `Node.invariant`, `Node.definition`, `Param`, `allows`/`forbids` and the
required `forbids`, `.expects`, `.keeps`/`.exempt`, alternative definitions, `eval_i` and `probe_j`.

Kept, with a test and an example use each: `race`, `guarantee`/`bracket`, `timeout`, `parTupled`, `ifM`.
Property-based testing stays in full and carries every check the running service made.

Changed in the user's source: the owner's concepts and no others (owner §15): three kinds of nodes (`Node.claim`,
`Node.assumption`, `Node.design`), two kinds of values (`Declaration`, `Definition`, given meanings by
`implementProven`, `implementTested`, `implementValue`, `implementProvided`, or by `define` and `program` on the
spot), two quantifiers (`forall`, `always`); the world outside said by assumptions (`behavesAs`, `initially`,
`writtenOnlyBy`, `changedOneRunAtATime`), each claim resting on one listing it with `.assuming`; what comes from
outside a type of its own, with an assumption of `always` on it, instead of assumptions on what calls a Definition
(`calledOnlyWith`); examples as tests beside the model (`FrFlowExamples`, `example`, `is`, `:=`); `env(d)` for
`p.value`; tagless boundaries and programs; names from the val as written; `implies` with chains in parentheses; a
program's claim as a run from a world; `.refines`; `when(…)(…).otherwise(…)`; `stored.in(world)`; a model
declared with its instance and checked by `checkedAgainst`; `derives LeanType` on domain types.

Added: consistency and vacuity proven in Lean (`consistent_<i>`, `start_<node>`, `inhabited_<node>`,
`satisfiable_<i>_<node>`, with derived or searched witnesses, "consistency not proven" a status of its own);
`made_<maker>` for every maker of an `always[T]`'s values; each example checked against the claims (`example_<i>`) and
the code; `show` saying how each claim is checked.

Unchanged in the user's source: every other term operation, `define`, `forall`, `b.start`, `.on[Case]`, the folds,
`let`. Underneath, terms are final (algebras and interpreters), each printed by `Printed` and run by `Evaluate` only.
