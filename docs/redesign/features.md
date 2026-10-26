# r43 appendix: feature audit (revision 15: the owner's core concepts applied; terms in tagless-final style)

Every user-visible feature and DSL operation, the concept it belongs to in the target (section 4 of
`r43-architecture.md`), where the examples use it, and what the rebuild does with it. The owner has decided (section
4.8 of the architecture, and `r43-owner-changes.md` §2 and §5); this table applies the decisions, and the rebuild
plan (section 6) says when each example is ported. Revision 8 changes how terms are represented (algebras with
interpreters, binders as host functions; 4.13), not what the user writes. Revision 9 applies the owner's forms
(`r43-owner-changes.md` §6, which today's library adopts too): names from the `val`, `implies` for `==>`, a contract
written as a claim, `.refines` for `.under`, `allows`/`forbids` for `expect`/`reject`; and every term construct below
is an algebra operation, printed by the one printer and run by the one evaluator. Revision 10 (review round 9):
`Operation[F]` and `Open[A]` for `Param` (the owner's names), `returning` for `result` in examples, a contract
naming its operation when its formula applies two, a flow contract written as a run from a world, the owner's list
relations, and a domain type's `LeanType` derived once (`derives LeanType`). Revision 11 (round 10, owner §9): a
contract may be the root (rooms' is the statement about `book`), a node with proven code is proven from its parts by
`impl`, a run states both outcomes in one formula, and a missing `derives LeanType` is named. Revision 12 (round 11):
a boundary is named from its val, and its model is written as an instance of its trait, elaborated, printed as
`Boundaries.lean` and run against an adapter by the model tests. Revision 13 (round 12, owner §10): one idea per
statement, what always holds an invariant (of a type's values, of a store's state); and the README readers' forms:
`stored.in(before)`, `store.model(…)(Stored(_))`, `when(…)(…).otherwise(…)`, `stored.checkedAgainst(start = …,
observe = …)`, `.assuming`, one contract shape naming its operation, ids the vals' names as written; and several root
statements, on any operations (owner §11). Revision 14 (owner §10–§18; architecture 4.14) says every feature in the
owner's core concepts and no others: three kinds of nodes (`Node.claim`, `Node.assumption`, `Node.design`), two kinds
of values (`Declaration[A]`, abstract, only in statements; `Definition[A]`, given its meaning by proven code, tested
Scala, a fixed value or a value provided where the code runs), two quantifiers (`forall`, `always`). Contracts,
invariants, models and definitions as kinds of node, `Operation`/`Open`, `allows`/`forbids` and `expects` are gone
under every name; examples are tests beside the knowledge base; the world outside is said by assumptions; the
theory is proven consistent and not vacuous in Lean. Revision 15 (review round 14): `define` and `program` give a
`Definition` carrying its meaning, the one user type (`Def1`, `Def2`, `Steps` gone); premises are written with
`.assuming`, the derivation only checking the list; today's library's names (`FrFlowExamples`,
`changedOneRunAtATime`, `initially`); `implementProvided`; `made_<maker>`; claims tested whole; the calendar's
claims over `RoomBookings`. Where a row below says what an earlier revision did, its last revision is the one that
holds.

Use counts are occurrences in `examples/*/src` (auth, keycloak, crm, sharing; rooms is noted where it adds a use),
measured with grep on 3aa8cd7 and checked on e0fa3d9. "Tests only" means only FrFlow's own suites use it.

## The DSL: vocabulary and terms (concept: Vocabulary, Term; the IR `Expr` made from each term)

| Feature | Target concept | auth / keycloak / crm / sharing | Rebuild |
|---|---|---|---|
| `Opaque(name, means)`, `User.T` | `vocab.Sort` | all | change: `Opaque(means)`, the name from the val |
| `Param[T](name, means)` (fact or operation) | `vocab.Symbol` with its `ValueKind`; `Named.param`; `dsl.vocab.Declaration`, `Definition` | all | change (owner §14, §15; it replaces revision 10's `Operation`/`Open`): `Declaration[A](means)` for a value only statements speak of (auth's `access`, `authorized`, `signedIn`: applied only under `Stating`, so code using one does not compile), `Definition[A](means)` for a value code uses, given its meaning once (`implementProven`, `implementTested`, `implementValue`, `provided`); each of any type, named from its val (`val granted = Definition[…](…)` is `granted`); `Problem.Undefined`, `DeclarationInCode` (`FormsSuite`, `AuthSuite`) |
| `Param` without a Lean type (code-only) | `SymbolType.CodeOnly`; one a statement mentions is `Problem.CodeOnlyInStatement` | crm, sharing (connections) | keep, as a Definition without a `LeanType`, `provided` where the code runs |
| `define { … }` (0 to 6 inputs), `program { … }` | a `Definition` carrying its meaning (owner §15, R14.2): `Definition.onTheSpot` (`Code.Proven`/`ProvenFlow`, its written lambda, the define's `core.term.Body`, whose body is a `lam` per input); `vocab.Define` (its term and IR in `Written`); `dsl.shape.Defines`, named as its val at compile time; called by `Definition.apply` (`Named.define`, `Functions.app` one argument at a time), passed as a function by `DefinitionSyntax`, printed once as its Lean `def`, run by the evaluator | 0 / 18 / 30 / 58 | change: `val covers = define { … }` is a `Definition[(Booking, BigInt) => Boolean]`; `Def1`, `Def2`, `Steps` are gone; a meaning is given once (`MeantWhereWritten`) |
| `object X extends Data[X]` | `LeanType` derivation (`DataMacros`), once per type: `enum X derives LeanType` (and `final case class … derives LeanType`); `Data[X]` keeps only the constructor on terms (`Claims(r, u, rs)`) | 1 / 4 / 13 / 23 | change: add `derives LeanType` to each domain type (revision 9's derivation at every use passed the JVM's size limits on sharing's largest file, 4.13); forgetting it says "X is not a domain type yet: add derives LeanType to its declaration" |
| `b.start` (a record's field) | `Records.field` by a `Selector` with Scala's getter, derived per record from its `Mirror` | all | keep |
| `==` on terms refused with a message | `Term.NoEquality` (today's message) | — | keep |
| `LeanType.product[T]`, `LeanType.sum[T]` | the same derivation, without the term constructor | sharing 8 + 5 | keep |
| `===`, `=!=`, `&&`, `\|\|`, `!` | `Logic`, `Equality` algebras (`Expr.Prim` in the IR) | all | keep |
| `==>` | `Logic.implies` | all | change: `implies`, alphanumeric, so it binds last (`a && b implies c` is `(a && b) implies c`); `==>` deleted, since its precedence (that of `=`) bound it tighter than `&&` and `\|\|`; a chain `a implies b implies c` (which Scala groups to the left) does not compile unless its grouping is written in parentheses |
| `True`, `False` | `Logic.bool` | — | keep (a Scala `Boolean` is not made a term implicitly) |
| `forall`, `exists` | `Quantifiers` algebra; the body a host function, its variable named by each interpreter where it binds it (no numbering) | 4+2 / 14+2 / 17 / 37 | keep the syntax; the user never sees an interpreter |
| (new) `always[T](x => …)`, `always(stored)(s => …)` | `Quantifiers.always`; `Range.Made(ty)`, `Range.Reached(models)` read off the formula; `AlwaysSyntax` | rooms 2 | new (owner §13, §15): every value of `T` that can be made, every state the store reaches; a hypothesis everywhere (`Guarded`), kept by every writer (`cover_<op>`), met at the start (`start_<node>`), shown to admit a value (`inhabited_<node>`) (`AlwaysSuite`) |
| `.on[Case]` match (`.on(X.Case)` for a case without fields) | `Sums.cases`: an eliminator derived per type from `Mirror.SumOf` (`CaseMacros`), each arm a host function over the case's fields (`When`), the case found by a derived test, no cast; `Expr.Match` in the IR | 0 / 12 / 29 / 98 | keep (`ChangesSuite`) |
| `c.fold(a, b)`, `o.fold(z)(f)`, an `Either`'s fold | `Logic.cond`, `Options.foldOption`, `Eithers.foldEither` (with `left`, `right`); `Expr.If`, `Expr.Match` in the IR | 0 / 9 / 8 / 73 | change: a Boolean's is `when(c)(a).otherwise(b)` (`Conditional`; R12.1: a `fold` hid which branch is which), the option's and the either's folds kept (`ChangesSuite`, `BookSuite`) |
| `xs.foldLeft(z)((acc, x) => …)` | `Lists.foldLeft`, two host-function variables; `Expr.Fold` | not counted (`foldLeft` appears in crm, keycloak, sharing, but in Scala as well as in terms) | keep (`ChangesSuite`) |
| `let(v)(x => …)` | `Functions.let`; `Expr.Let` | sharing 5 | keep (`ChangesSuite`) |
| `make[R](fields…)`, `x.updated(_.field, v)` (a record made, copied) | `Records.construct` with a derived curried `Constructor`, `Records.copy` by the field's `Selector` (`set` through `copy`); `Expr.Make`, `Expr.Copy` | not counted (records are made in terms through today's constructors) | keep (`ChangesSuite`) |
| list, option, map, set operations | `Lists`, `Options` algebras, growing to today's set (`PrimOp`, `Iterate`, `Fold` in the IR) | all | keep |
| `xs.allDistinct`, `xs.pairwise(r)`, `xs.forall(d)` with a define (owner §4, today's `ListRelations`) | `Lists.nodup`, `Lists.pairwise` (two host-function variables), printed `(List.Nodup xs)` and `(List.Pairwise (fun (a : A) (b : A) => …) xs)`; a define is a function of terms, so `forall` takes it | rooms 3 | keep (`RoomsSuite`, the generator) |
| a project's own operation (`count`) | a define; or an algebra outside the core with its meaning in the core and, optionally, interpreters that know it (`Count`, 4.13) | — | keep |
| `BigInt` arithmetic; `Int`/`Long` compare only | `NumKind` | all | keep |
| `p.value` in plain code | `env(d)` on the values the code is given (`dsl.kb.ValuesSyntax`), `d` a Definition | 34 | change (owner B: no ambient state); every use rewritten when its example is ported |
| `d.fn` in plain code | `d.fn(env)` (`eval.term.DefSyntax`): the define's term run by the evaluator (`Evaluate`, curried), nothing compiled | 8 (main) | change: the values passed explicitly |

## The DSL: nodes (concept: Statement, Edge)

| Feature | Target | Use | Rebuild |
|---|---|---|---|
| `Node.claim`, `Node.contract`, `Node.assumption`, `Node.invariant`, `Node.definition`, `Node.design` | `Statement`: `Claim`, `Assumption`, `Design` (owner §15) | all | change: three forms only, `Node.claim(statement)(formula)`, `Node.assumption(statement)(formula)`, `Node.design(statement)(paths*)`, without `why` and without the id (the id is the val's name as written, R12.1); `Node.contract`, `Node.invariant`, `Node.definition` removed, said as the rows below say (`FormsSuite`); how each claim is checked is derived and shown (`Checking`, `Says.checking`, `CheckingSuite`) |
| `Node.invariant[A, B](statement, why, scope)(rule)` and conditions glued into statements with `&&` | a claim of `always`: `Node.claim(statement)(always[Booking](b => …))`, `Node.claim(statement)(always(stored)(held => …))` | crm 1, keycloak 1; rooms' hypotheses | change (owner §10, §13, §15): what always holds is its own claim of `always` (a hypothesis on every value in Lean, `Guarded`; checked where a tested Definition makes a value, `Made`; met by generated values, `Respecting`; kept by every program writing the store, `cover_<op>`); today's relation of answers (crm's `noCrossTenantRead`, keycloak's `realmIsolation`) becomes a claim `forall` over the Definitions it relates; `&&` gluing ideas is a style guide only, never checked (`AlwaysSuite`) |
| `Node.contract(op)((a, b, result) => …)` (the lambda form) | a claim on a Definition, read as a call where it applies the Definition to its leading variables (`CallForms`: `CallForm.Call`, its post by `Opened`) | all | change (owner §15): `Node.claim(statement)(forall((a, b) => op(a, b) === …))`; the call reading is derived, never a kind, and a claim reading as no call is checked as a whole; another Definition on the same inputs is an ordinary mention (`FormsSuite`, `CrmClaimsSuite`) |
| a flow contract's lambda `(input, result, before, after) => …` | a claim read as a run (`CallForm.Run`, its post a run opened: `Worlds.runs`, `Opened`) | crm 1, sharing 3 | change: a claim, `forall((now, before) => runExpiry(now).from(before) { (result, after) => … })`, a model's state `databaseModel.in(before)` (`ModelState.in`; was `before(databaseModel)`, R12.1); the post is over today's four inputs, so Lean is unchanged (`ExpiryJob` byte for byte) |
| `why = "…"` on every node | none: the reason is the signed decision's (`Decision.reason`), shown by `show` and review (`Says.reason`) | 10 / 23 / 26 / 58 (rooms 2) | remove (owner); the texts go into each example's first decisions' reasons when the owner decides them |
| `idea = "Section"`, `KnowledgeBase(…, idea = …)` | none | 77, all four | remove (owner, revision 2) |
| `Node.assumption(store)(Stored)(statement)` (a boundary's model, `object Stored extends Bookings, StateModel[…]`) | the model in the vocabulary (`StateModel`, `BoundarySig`) and an assumption about the outside, `OutsideFact.BehavesAs`; Lean's `Boundaries` module (`LowerModels`); `World.models` in Scala | crm, sharing, rooms | change: `final class Stored[F[_]: Flow](state: Model[F, S]) extends Bookings[F, Term]` (the model an instance of the tagless trait over its state), declared with its boundary, `val stored = store.model(means)(Stored(_))` (`StoreModel`), and assumed by `Node.assumption(statement)(store.behavesAs(stored))` (owner §16); a premise of every check of code calling the store, written `.assuming(storeModel)`, never a part |
| (new) the world outside: `stored.initially(rule)`, `stored.writtenOnlyBy(programs*)`, `stored.changedOneRunAtATime`, `outside.calls(d)` (today's library's names, R14.4) | `OutsideFact` (`Initially`, `WrittenOnlyBy`, `OneRunAtATime`, `Calls`), each said by an assumption and listed by each claim resting on it (`.assuming`); `Premises` (a check), `PremiseMissing`, `PremiseNotNeeded`, `WriterNotListed` | rooms 4 | new (owner §16, §17): the facts the rules about `always` rest on (the start, the only writers, one run at a time, the values the outside calls with), each reviewed as any node; atomicity assumed, asynchrony future work; `show` lists each fact a check rests on (`BookSuite`, `CheckingSuite`) |
| `Boundary[B]("store", means)` | `BoundarySig`; `BoundaryOps[B]` | crm, sharing, rooms | change: `Boundary[B](means)`, named from its val; `trait B[F[_], T[_]] derives BoundaryOps` |
| `.under(parents*)`, `.replaces(other)` | `Edge.PartOf`, `Edge.Replaces` | all; replaces none | change: `.refines(parents*)` for `.under`; `.replaces` kept |
| (new) `.assuming(premise*)` | `Edge.Assumes`: a premise the node's proof assumes (an assumption, or a claim of `always`), beside its parts | rooms | new (R12.1): a premise, never a part; `PremiseNotAssumed`, `OutsideAsPart`, `OutsideClaimed`; the one mechanism for a premise, the outside's included (R14.3): the list is checked against what the check rests on (`PremiseMissing`, `PremiseNotNeeded`) |
| `.keeps(invariant)(view)`, `.exempt(invariant, because)` | none | keycloak, crm | **remove** (owner §15): who keeps an `always` is derived (`Scope`), and a claim mentions only what it constrains, so nothing is exempt; the relation of answers is a claim over the Definitions it relates |
| two definitions of one term as alternatives | none | none in examples | **remove** (owner §15): a Definition has one meaning; alternatives are two claims, one `.replaces` the other |
| `Node.definition(…)(authorized := …)` (a definition node, `substs`) | a claim of one equation (`authorized(u, p) === grants.exists(…)`), or a `define`; a value fixed in the model is `implementValue(d)(v)` | auth 3, crm, sharing | change (owner §15): the equation is also the Declaration's consistency witness (`AuthSuite`) |
| `.examples(bindings*)(expect/reject…)` | `core.example.Example(name, givens, fact)`; `dsl.example` (`FrFlowExamples`, `example`, `is`, `:=`); `eval.run.ExampleRun`, `OnCode`; `proof.whole.ExampleGoals`; `api.view.OnClaims` | 1 / 4 / 10 / 29 | change (owner §18, R14.4): examples leave the nodes, ordinary tests beside the knowledge base, `class GrantedExamples extends FrFlowExamples(rooms): example("back to back: granted"): granted(…) is true`; checked against the code and, in Lean, against the claims (`example_<i>`); one setting provided values "checked in Scala only"; nothing depends on them; `allows`/`forbids`, `Call` and the rule that a contract has a `forbids` are removed (`ExamplesSuite`, `ExampleRunSuite`) |
| `bind`, `bindTable` | `example.Given` | bind all; bindTable auth 1 | change: `d := value` in an example, `d` a provided Definition (a table is a value of its type) |
| `.expects(statement)(consequence)` | a claim the expecting claim refines | crm 4 | change (owner §15): the consequence is its own claim, `.refines`d by the expecting one, so `complete` proves it from its parts; `expect_i` goes |
| `.checkedBy(check)` | none | keycloak 1, crm 4 | **remove** (owner: a cheaper check was for run time); its Lean obligation `check` (post implies check) goes with it |
| `.checkedAtRunTime(RunCheck)` | none | tests only | **remove** (owner) |
| `.leftOpenAbove` | `Claim.reliance = LeftOpen`, a content field | sharing 5 | keep, on a claim only (`Fault.NotAClaim` on an assumption) |
| `.failsChangingNothing[E]`, `.onFailure[E]` | `CallForm.Run.failure: FailureClause`, read off the formula | sharing 2 / 1 | change: `.failsChangingNothing[E]` on the run in the formula (`Ran`); `.onFailure` the failing side of the claim's own run, one formula for both outcomes: `handle(r).from(before) { (answer, after) => … }.failing { (error: Term[E], after) => … }` (`SharingClaimsSuite`) |
| `.checkedAgainst(start, read)`, `.implementedBy(start, read)` | `AdapterCheck`, run by `testing.ModelTests.run` (generated runs from the boundary's signature, `Runs`; answers then states compared); `CodeTable.realized` (`Outside`, `Own`) | crm 1+2, sharing 1+3 | change: on the model, named arguments, `stored.checkedAgainst(start = held => …, observe = adapter => …)` (R12.1; `StoreModelSuite`); now the only check of an outside system's adapter |

## The DSL: code (concept: Code, testing)

| Feature | Target | Use | Rebuild |
|---|---|---|---|
| `kb.implement(c, calls*)(code)` | `Code.Tested`; the code is `env => f` over the values it is given | 3 / 2 / 3 / 1 (rooms 1) | change: `implementTested(d, calls*)(env => code)` on a Definition (owner B, §15), tested against every claim mentioning `d` |
| `kb.implementProven(c)(define)`, `(define, runs)` | `Code.Proven` | keycloak, crm, sharing | change: `implementProven(d)(define)` on a Definition; `ProvenBeside` goes (the runs beside a define are a tested Definition of their own) |
| (new) `kb.implementValue(d)(v)`, `kb.implementProvided(d*)` (revision 14's `provided`, R14.7) | `Code.Valued`, `Code.Provided` | auth (`grants`, `sessions` provided) | new (owner §15): a value fixed in the model (substituted in Lean), a value given where the code runs (bound by an example, drawn by a test, passed in production; Lean states every claim for every such value) |
| `kb.implementProven(job)(flow)` | `Code.ProvenFlow`: a program recorded (`program { … }`) | crm, sharing, rooms | change: `implementProven(book)(bookIfGranted)` on the Definition; the program is tagless (owner C); `impl` is asked of its run on the models (`f_run`) for each claim mentioning it |
| `kb.service(c)(bindings*)` | `knowledge.code(d)(bindings*)`: the same wiring (`eval.run.Wiring`), no check | 2 / 4 / 10 / 22 | change (owner: no run-time checking); servers call the code directly and lose their `ContractViolation` branches |
| `kb.run[F](contract)(bound*)` | the program called directly: `Running.make[IO](denote, env)` and `database.lifted(adapter, running)` | crm 2, sharing 3 | change (owner C) |
| `kb.reporting(v => …)`, `Violation`, `ContractViolation` | none | crm, keycloak servers catch it; suites intercept it | **remove** (owner) |
| `kb.generating(gen)`, `Gen.derived`, `.describedAs` | `example.Gen` (data) + `testing.Draw` | crm 1, sharing 12 (rooms 2) | keep |
| `kb.testedWith(TestSettings)` | `testing.Settings` from `project.Config` | tests only | move to the checker's configuration |
| `FRFLOW_SEED=fresh` | `project.Config` | CI doc | keep |

## Programs over boundaries (concept: Prog; owner C: tagless boundaries)

| Feature | Target | Use | Rebuild |
|---|---|---|---|
| `trait Database { def load: Flow[CrmStore] }`, `Boundary[T]` | `trait Database[F[_], T[_]] { def load: F[T[CrmStore]] }`, `Boundary[Database](name, means)`; `BoundaryOps` derived (signatures, a recording instance, a by-name caller for tests, a lifted adapter, the model read) | crm 1, sharing 1+2 | change: the examples' boundaries are rewritten |
| a program as a `Flow[A]` value | `final class Job[F[_]: Flow](db: Database[F, Term])`: values are `Term`s, the effect is abstract; `program { (a: Term[A]) => Job(database.recording).run(a) }` records it for Lean | crm, sharing | change (owner C) |
| production implementations returning `Flow.effect(x)(f)` | adapters written as `Database[IO, Id]` over plain values; `database.lifted(adapter, running)` gives programs their `Database[IO, Term]` | crm 9, sharing 5 | change: `Flow.effect` goes |
| `StateModel[S]`, `state.get/set/update` | a model is an instance of the boundary trait over `Model[F, S]`'s state (`Model.recorded`), read into `vocab.StateModel` | crm 1, sharing 2 | change in form, same meaning |
| `for`/`flatMap`/`map`, `pure`, `*>`, `as`, `void`, `<*`, `flatTap`, `tupled`, `sequence` | cats syntax on any `F[_]: Flow` (a `Monad`); `Prog.Bind`, `Pure`, `Let` | crm, sharing | keep (from cats, not FrFlow's own) |
| `traverse_`, `traverse`, `foldM` | `Flow.each` (written, with its element's `LeanType`; `RecordingSuite`), `collect`, `fold` (`Prog.Loop`, `Collect`, `Accumulate`) | crm, sharing | keep |
| `c.foldF`, `whenA`, `unlessA` | `Flow.cond` (`Prog.Branch`) | whenA sharing 3 | keep |
| `ifM` | `Flow.ifM` | tests only | **keep (owner)**, with a test (`RecordingSuite`) and a use in an example (crm, step 12) |
| `raiseError`, `handleErrorWith`, `attempt`, `retry(Schedule)` | `Flow.raise`, `handle` (written in `Recording` and `Running`, tested), `attempt`; retry as handle + clock | sharing 7 + 1 | keep |
| `guarantee`, `bracket` | `Flow.guarantee` (`Prog.Guard`, with its reading), `bracket` made of it | tests only | **keep (owner)**, tests, and a use in sharing (step 13) |
| `timeout(seconds)` | `Flow.timeout(clock)`: the clock read around the program, nothing cancelled (as today) | tests only | **keep (owner)**, test, use in sharing (step 13) |
| `parTupled` | `Flow.parTupled` (`Prog.Par` + `commute_i`) | tests only | **keep (owner)**, test, use in sharing (step 13) |
| `parTraverse`, `parTraverseN` | `Flow.parCollect` (`Prog.ParEach` + `commute_i`) | sharing 3 | keep |
| `race` + the `Races` boundary | `Flow.race` (`Prog.Race`, read as the scheduler's choice) | tests only | **keep (owner)**, test, use in sharing (step 13) |
| `atomically` | `Flow.atomically` (`Prog.Atomic`; a `Mutex` in production) | sharing 5 | keep |
| `Flow.now`, `sleep`, `waitUntil`, `Clock`, `ClockModel`, `FakeClock`, `SystemClock` | `Clock[F, T]`, FrFlow's own boundary, with its model; `FakeClock` an instance for tests | sharing | keep |
| `Flow.every(period)(job)` | scheduler over a program | sharing 2 | keep |
| `FaultPlan`, `World(…)`, `Failed(…)` in examples | values in an example's fact (a world made, a run's outcome stated) | crm 10, sharing 3+8 | change: written in the example's fact; `RunExample`, `RunEnd` go |

## Checks Lean makes (concept: Obligation)

| Obligation | Target | Rebuild |
|---|---|---|
| `complete`, `holds`, `root_impl`, `impl` | `Prop.Implies` over `ClaimOf` | keep; `impl` is the step of a node with proven code from its parts (the claims about what the code calls), so `complete` is not asked of it (round 10; rooms' root, `BookSuite`) |
| the root: a claim or invariant without parents | `Refinement.roots` | change (owner §11): several root statements, the claims without parents, on any Definitions and Declarations, a statement relating them included; no `SeveralRoots` problem, keeping them a concise few is the author's. A service's purpose about its entry program is one (owner §9; rooms' `bookWhenFree` and `answersWhetherBooked`, beside its two claims of `always`) |
| `needed_C`, `vacuous`, `restates`, `clash`, `unsat` (tries) | `TryKind` | keep |
| `restates_i_C`, `idle`, `feasible`, `cover_X`, `expect_i` | as today | keep, but `expect_i` (gone with `expects`); `cover_<op>` per program writing a store, for each `always` about it |
| (new) `start_<node>`, `made_<maker>`, `inhabited_<node>` | `Prop.Starts`, `Prop.Makes` (`Required.made`, `proof.terms.Making`, `LowerKeeps.makes`), `Prop.Inhabited` (`proof.whole.Joint`, `Possible`) | new (owner §13, §18, R14.1): every state a store may start in (`initially`) meets what always holds of it; every result of a proven define or a store operation on its model meets each `always[T]` its guard applies to (rooms' two `made_inRoom`, proven); each `always[T]` admits a value, its witness found by the search |
| (new) `consistent_<i>` | `Prop.ForEvery`/`ForSome` over a group's open values (`Joint`), discharged by `Discharge.Witnessed` (`LowerWitness`, `frflow_witness`) | new (owner §18): the bottom statements and the assumptions beside them, grouped by shared open values, jointly satisfiable for every value provided; witnesses from equations, bounds and proven code; else "consistency not proven", its own status (`ConsistencySuite`, `AuthSuite`) |
| (new) `satisfiable_<i>_<node>` | `Vacuity.Satisfiable` (`Conditions`), `Possible` | new (owner §18): each condition `A` of `A implies B` can hold; a witness from the search, else stated only, "not shown" (`VacuitySuite`) |
| (new) `example_<i>` | `proof.whole.ExampleGoals`, a try (`frflow_example`) | new (owner §18): each example follows from the claims constraining what it mentions; nothing depends on it |
| `check` (post implies `checkedBy`) | none | **remove** with `checkedBy` |
| `eval_i`, `probe_j` (Lean vs Scala) | none | **remove** (owner §18): examples are checked against the claims in Lean and against the code in Scala, separately; `Prop.Evaluates`, `LeanAndScalaDisagree` go |
| `commute_i` | `Prop.Commutes` | keep, for `parTupled` and `parCollect` |
| a failed step refuted by a case Lean proves (since 3aa8cd7) | `testing.search.StepRefutation` finds the case, `proof.layout.RefutesModule` states it | keep |
| the contradiction search (`unsat`, `clash`) | `TryKind` | keep, as an early refuter only (owner §18): consistency is never inferred from it |
| authored proofs, `scaffold`, proof rules | `Discharge.Authored`, `proof.reading` | keep |

## Tests (concept: testing; owner: property-based testing stays in full)

| Feature | Target | Rebuild |
|---|---|---|
| property tests of plain code against its contract: derived generators, seeded by the examples, shrinking, coverage of a claim's parts, counterexamples saved and replayed, the `.frflow/tests.json` cache | `testing.PropertyTests` (each case: the inputs drawn, the values the code reads made by `eval.run.Wiring`, the call through `Fn`, judged by `eval.run.CallCheck`), `Hits`, `report.*` | keep, against every claim mentioning the tested Definition (per call where the claim reads as one, else the claim evaluated whole on its drawn variables, R14.5; a claim with no Scala value "not checked", `Warning.NotChecked`); `PropertyTests.of` written (`CalendarSuite`: the README's calendar on 500 cases meeting what always holds); shrinking and the cache are step 5's; what the running service checked on each call is checked here, before production |
| an outside system's adapter against its promise (crm's `recordsByQuery`, keycloak's `sessionLookup`) | `PropertyTests` on the adapter's code against its assumption's formula, and the examples (`ExampleRun`) | keep; replaces the run-time check of every adapter call |
| model tests of `implementedBy`/`checkedAgainst` (generated runs, shrinking) | `testing.ModelTests.run` of an `AdapterCheck` over two `World`s (the adapter, `BoundaryOps.call`; the model, `World.models`), runs generated by `Runs` through `Respecting` | keep (`StoreModelSuite`: rooms' store against its model on generated runs, by `stored.checkedAgainst(start = …, observe = …)`) |
| fault sweep, interleavings | `testing.Interleavings[F[_]: Async: Random]` over the recorded program run on the adapters | keep |
| the step-refutation search | `testing.search.StepRefutation` | keep |
| (new) the witness search | `testing.search.Witnesses` over the generators and `Small` (SmallCheck-style small values, at most 5,000 candidates, judged by the evaluator) | new (owner §18): witnesses of vacuity, given to Lean |
| a contract changed under unchanged code ("the contract changed and its code no longer meets it") | `decision.review.Cause.movedUnderCode`, said by the CLI | keep, said of the claim |

## Run time (removed: owner, "FrFlow is for testing before production and strict static guarantees")

| Feature | Rebuild |
|---|---|
| the `runtime` module: `service` wrapping code to check each call (`enforce`, `Service`, `Guard`), sampling (`RunCheck`, `checkedAtRunTime`), the assumption watch, the violation reporter, `ContractViolation` | **removed**; section 4.12 of the architecture says what this removes and what moved to tests |
| facts about the values a service runs with, checked when wired and on change (sharing's `HousekeepingOnTime`, "the server checks it as it runs") | trusted, as every assumption; checked under the examples' `:=` values and the tests' values only |

## Decisions and review (concept: Content, Ledger, review)

| Feature | Target | Rebuild |
|---|---|---|
| accept / reject / confirm / revisit / gone, `-m`, `--yes`, `--revisit` | `rules.Decide`, one rule per command | keep |
| causes, rewording, mechanical batch, refusals | `review.*`, `rules.*` | keep |
| signed decisions, keys filed in `.frflow/keys/<name>.pub`, "keys count as committed" (since 3aa8cd7) | **a committed, developer-signed list of who may decide** (`.frflow/deciders`, `ledger.Deciders`): a decision counts only when its key is listed under its decider's name; each version of the list is signed by a key the version before it listed; FrFlow reads the committed versions only | change (owner); filing a new key under a new name decides nothing |
| ledger file | `wire` codec of `Ledger`, the new payload | new format; old ledgers are not read (owner: fresh ledgers) |
| content forms `V1`/`V2`, `confirm --rebind`, `Retired` (old `IDEA` entries), `Text` fingerprints | none | **removed** (owner: fresh ledgers) |
| code cause from governed files | `CodeFingerprint` by the simple lexer: comments stripped, lines and indentation kept | change (owner F) |
| held aside by a layer | `Views.inbox(aside)` | keep |

## Front ends

| Feature | Target | Rebuild |
|---|---|---|
| `tree`, `show [--full]`, `diff`, `inbox`, `find`, `review`, `render`, `check [NODE]`, `scaffold`, `status`, `ci`, `--json`, `--plain`, exit codes | `cli` over `api.Reading/Deciding/Proving` | keep; `show` and review give the reason from the decision, and `show` how each claim is checked (`Says.checking`); `status` the consistency groups and examples (`WholeView`, `Warning.ConsistencyNotProven`) |
| web view | `web` over the same algebras | keep |
| `CliExtension`, `WebExtension` | `api.Extension` | keep |
| `frflowInit`, `frflowInitAgent` | `cli.Init`, `agent.Init`; `init` also writes `.frflow/deciders` signed by the developer's key | keep |
| agent layer | `agent` over `api`; its proposals carry their rationale in the request or conversation, not in the node | keep; questions have no numbers |
| `bench/`, `examples/scale` | tooling | keep, rebuilt last |
| `.frflow/kb.json` | `wire.snapshot` rows, made by `Rows` | keep every fact, regrouped by kind; with the consistency groups (`GroupRow`) and the examples (`ExampleRow`) |

## Summary

Removed: the `runtime` module and everything only it used (`service`'s checks, `checkedBy` and its `check`
obligation, `checkedAtRunTime`/`RunCheck`, sampling, the assumption watch, the reporter, `ContractViolation`), `why` on
nodes, the ambient scopes (`Param.value`, fresh-variable counter) and any numbering of variables before an
interpreter binds them, today's `Flow` values and `Flow.effect`, content
forms and `confirm --rebind`, `Retired`, `Text` fingerprints, filed keys as authority. Kept, now with tests and an
example use each: `race`, `guarantee`/`bracket`, `timeout`, `parTupled`, `ifM`. Changed in the user's source:
`env(d)` for `p.value`, `implementTested(d)(env => …)`, tagless boundaries and programs, nodes without `why`; by
revision 9's, 10's and 13's forms, names from the val as written, `implies` (a chain in parentheses), a program's
claim as a run from a world, `.refines`, `.assuming`, `when(…)(…).otherwise(…)`, `stored.in(world)`, a model declared
with its instance and checked by `checkedAgainst`, `derives LeanType` on domain types; and by revision 14's (owner
§10–§18) the core concepts and no others: three kinds of nodes (`Node.claim`, `Node.assumption`, `Node.design`), two
kinds of values (`Declaration`, `Definition`; `implementProven`, `implementTested`, `implementValue`,
`implementProvided`; `define` and `program` a Definition carrying its meaning), two quantifiers (`forall`, `always`);
the world outside said by assumptions (`behavesAs`, `initially`, `writtenOnlyBy`, `changedOneRunAtATime`,
`outside.calls`), each claim resting on one listing it with `.assuming`; examples as tests beside the knowledge base
(`FrFlowExamples`, `example`, `is`, `:=`). Removed by revision 14: `Node.contract`, `Node.invariant`, `Node.definition`, `Operation`, `Open`,
`allows`/`forbids` and the required `forbids`, `.expects`, `.keeps`/`.exempt`, `Choice`, `ProvenBeside`, `eval_i` and
`probe_j`. Added: consistency and vacuity proven in Lean (`consistent_<i>`, `start_<node>`, `inhabited_<node>`,
`satisfiable_<i>_<node>`, with derived or searched witnesses, "consistency not proven" a status of its own), each
example checked against the claims (`example_<i>`) and the code, `show` saying how each claim is checked, and (revision
15) `made_<maker>` for every maker of an `always[T]`'s values. Removed by revision 15: `Def1`, `Def2`, `Steps`,
`provided`, `startsWith`, `oneRunAtATime`, `Examples(kb)(…)`, derived premise links.
Property-based testing stays in full and carries every check the running service made. Unchanged in the user's
source: every other term operation, `define`, `forall`, `b.start`, `.on[Case]`, the folds, `let`; terms are final
(algebras and interpreters) underneath, each printed by `Printed` and run by `Evaluate` only.
