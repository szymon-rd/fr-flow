# FrFlow: architecture review and redesign (r43, revision 15)

> In this repository: the planned code (`r43-design/` in the text) is `docs/redesign/planned/`, the Lean spike (`r43-spike/rooms-lean-r15/`) is `docs/redesign/lean-spike/`, the tools (`r43tools/`) are `docs/redesign/tools/`, the owner's decisions are `docs/redesign/owner-decisions.md`, and the approving review is `docs/redesign/review.md`.


Measured on branch `claude/kind-bardeen-465vv8` at `3aa8cd7`; what changed since, up to `e0fa3d9` (the `rooms`
example, the step refutation, keys counted as committed), is in 2.6. Revision 7 applied the owner's decisions on 4.8
and on the feature audit (`r43-owner-changes.md` §2): a ground-up rebuild in this repository, fresh ledgers, no
run-time checking, tagless boundaries, no ambient state, nodes without `why`, a signed list of who may decide.
Revision 8 answers review round 7 and applies the owner's decision that terms follow Kiselyov's tagless-final course
(`r43-owner-changes.md` §5): the term language is a set of algebras with interpreters, binders are host functions,
the user's `Term[A]` stays closed and concrete (4.13).
Revision 9 answers review round 8 and the owner's forms (`r43-owner-changes.md` §6): obligations and programs hold
terms, so the Lean printer and the evaluator are the only printer and evaluator of terms and the IR is read only by
the analyses; matching, `make`, `copy`, the folds, `let` and `Either` are algebras; `lam`/`app` replace the arity
families; the user writes names from the `val`, `implies`, a contract as a claim, `.refines` and `allows`/`forbids`.
Revision 10 answers review round 9: a contract relating its operation to another on the same inputs names its
operation; a program's runs are an algebra, so a flow contract and its failure clause are written as claims; an
unparenthesised chain of `implies` is refused; `Operation[F]` and `Open[A]` (the owner's names) replace `Param`;
`allDistinct`, `pairwise` and `forall` of a define are carried; a domain type derives its `LeanType` once.
Revision 11 answers review round 10 and the owner's root for rooms (`r43-owner-changes.md` §9): any stated node
without parents may be the root, contracts included; a node whose code is proven is proven from its parts by `impl`
(its parts the promises of what the code calls, and the models of the boundaries it calls), which replaces
`complete` for it; rooms' root is the statement about the `book` flow; a run states both outcomes in one formula;
a type missing `derives LeanType` is named with what to add. Revision 12 answers review round 11: a boundary's model
is written as an instance of the boundary's trait over its state, as a program is over its boundaries, taken by
`Node.assumption`, elaborated into the vocabulary, printed as today's `Boundaries.lean` (crm's byte for byte, from its
boundary and model), and run in Scala, so a program's run is defined over it and an adapter is tested against it on
generated runs; a boundary is named from its val; `impl` over what the code relies on, for a node without parts, is
documented and tested. Revision 13 answers review round 12 and the owner's rule of one idea per statement
(`r43-owner-changes.md` §10): what always holds is an invariant, of a domain type's values (a hypothesis on every
value in Lean, checked where a value is made, met by generated values) or of a store's model state (assumed by every
contract, kept by every program, `cover_I`); rooms says each thing once, booking's contract in two one-equation
statements; the README readers' forms are fixed (`stored.in(before)`, `store.model(…)(Stored(_))`, `when(…)(…)
.otherwise(…)`, `stored.checkedAgainst(start = …, observe = …)`, `.assuming` for a premise, one contract shape naming
its operation, ids the vals' names as written); Lean accepts the printed rooms module and its obligations are proven
(9). The owner then replaced the one-root law (§11): several root statements, on any operations, are allowed.
Revision 14 applies the owner's core concepts (`r43-owner-changes.md` §10–§18; 4.14), strictly and under no other
name: three kinds of nodes (`Node.claim`, `Node.assumption`, `Node.design`); two kinds of values (`Declaration[A]`,
abstract and applied only where a statement is written; `Definition[A]`, of any type, given its meaning by proven
code, tested Scala, a value fixed in the model or a value provided where the code runs; `define { … }` a Definition
on the spot); two quantifiers (`forall`, every possible value; `always`, every value that can occur: `always[T]` of
what can be made, `always(stored)` of what a store reaches). A claim constrains every value it mentions, and its
obligations follow from its formula and from those meanings. The statements are proven consistent in Lean (groups
of statements sharing open values, witnesses derived from equations, bounds and proven code, "consistency not
proven" its own status) and not vacuous (`inhabited`, `satisfiable`, witnesses found by a search); examples are
ordinary tests outside the nodes, checked against the claims in Lean and against the code; what the world outside
does, atomicity included, is said by assumptions. Contracts, invariants, models and definitions as kinds of node,
`Operation`, `Open`, `allows`/`forbids` and the rule that every contract has a `forbids` are deleted (Lean compiles
rooms' and auth's modules: 4.14). Where 4.13 and 9 recount earlier revisions, the history is kept and says what
replaced it. Revision 15 answers review round 14 (`r43-review-14.md`, 4.14, 9): one user type for a Definition
(`define` and `program` return a `Definition` carrying its meaning; the core's `term.Definition` is `term.Body`;
`Def1`, `Def2`, `Steps` are gone); `.assuming` written in the source is the one mechanism for a premise, the
derivation only checking it; the calendar's claims range over what the store can give (`RoomBookings`, with its
`always`, made by the store's `inRoom` and taken by `granted`), so the README's binary-search calendar is correct as
stated, and `made_<maker>` is written and proven; today's library's names (`FrFlowExamples`,
`changedOneRunAtATime`, `initially`); claims about tested Scala that read as no call tested whole, "not checked" when
they have no Scala value; consistency groups solved in substitution order; `implementProvided` in the `implement…`
pattern; an example setting values shown "checked in Scala only"; each remaining stub given its step (6).
Appendices next to this file:

- `r43-deps.txt`: the measured package and module dependencies, cycles, cross-module use of internals.
- `r43-features.md`: every feature and DSL operation, its concept in the target, its use, and what the rebuild does.
- `r43-design/`: the planned code, an sbt project of nine modules (449 main files, 10,340 lines; 57 test files, 147
  tests). `cd r43-design && sbt clean compile proof/test decision/test dsl/test project/test evaluation/test
  testing/test` succeeds offline with `-Werror -Wunused:all -Wnonunit-statement -Wvalue-discard`, and all 147 tests
  pass:
  - four of crm's generated Lean files printed byte for byte from the Lean AST, with a post printed from its term, a
    flow's steps lowered around their terms, and two obligations (`impl`, `unsat`) lowered from `Prop` (today's Lean
    is now a reference, not a constraint; the test shows the AST can say it);
  - one test per authored-proof rule, and the lemmas' own rule;
  - a design re-parented is reviewed, a claim re-parented is not; a short reason is refused; a gone node's decision
    is reported; a decision counts only when its key is listed under its decider's name, and a new list of deciders
    only when a key of the list before it signed it;
  - every flow combinator recorded as the step Lean reads (`ifM`, `parTupled`, `race` and its reading, `guarantee`,
    `bracket`, `timeout`, `each`, `raise` and `handle`), a bound term shared as Lean's `let`, and a raced branch
    ending in a shared `let`;
  - one Definition (R14.2): `define` and `program` give a `Definition[(Booking, BigInt) => Boolean]` and a
    `Definition[Booking => Program[Boolean]]` carrying their meaning, `Def1` and `Steps` do not exist, a meaning is
    given once, and `implementProven` takes only a define or a program (`FormsSuite`);
  - three kinds of nodes and two kinds of values (owner §15): a contract, an invariant, a definition node and an
    operation do not exist; a Declaration used in a define or a program does not compile, saying why, and code for
    a Declaration does not compile; a claim applying a Definition to its leading variables reads as a call of it,
    one mentioning it elsewhere too is still a claim, checked as a whole; `.leftOpenAbove` on an assumption is a
    fault (`FormsSuite`, `NodeSyntaxSuite`);
  - the README's rooms in these concepts (`Rooms.scala`, `Book.scala`, `Calendar.scala`, `Knowledge.scala`):
    booking's two claims on `book` (one equation each) and what always holds, `always[Booking]`, `always(stored)`
    and `always[RoomBookings]`, the root statements; the calendar's claims on `granted` over what the store can
    give, tested against the README's binary-search calendar; five assumptions about the world outside, each claim
    resting on one listing it with `.assuming`, a list missing one or listing one not needed refused, naming what to
    write (R14.3); `impl` the root's step, `complete` the calendar's; the store's model and the program's run printed
    as Lean (`BookSuite`, `RoomsSuite`, golden files Lean compiled);
  - the calendar over what the store can give (R14.1): on 500 generated cases meeting what always holds it meets its
    claim; on two overlapping bookings of a room, which the store cannot give, it is wrong and no case draws them;
    the README's step-4 bug is found; `made_inRoom` printed (`CalendarSuite`, `AlwaysSuite`);
  - what always holds (owner §13): every booking a statement is about comes with `endsAfterStart` as a hypothesis;
    every run of booking's code keeps each `always` about the store (`cover_book`, `keeps_book`, golden files Lean
    compiled); a booking ending before it starts, at a tested Definition's boundary or inside a `RoomBookings`, breaks
    `endsAfterStart` (`AlwaysSuite`);
  - how each claim is checked, as `show` prints it, read off the formula and the meanings; a claim reading as no call
    tested whole, one with no Scala value "not checked" (R14.5, `CheckingSuite`);
  - consistency (owner §18): rooms' one group, the calendar's claim with `granted` open, witnessed by its equation,
    and the store's start meeting each `always` about it, as Lean (`ConsistencySuite`); auth's purpose over three
    Declarations, each its own group witnessed by the equation of the claim refining it, for every grant table
    provided, and with no such claim "consistency not proven"; the three as one group solved in substitution order,
    `access` witnessed after `signedIn` and `authorized` (R14.6, `AuthSuite`);
  - vacuity: each `always[T]` shown to admit a value, each condition of `A implies B` an obligation over the
    variables bound above it, a witness found by the search and given to Lean, a condition no value meets "not
    shown" (`ConsistencySuite`, `VacuitySuite`, `SmallSuite`);
  - examples as tests (owner §18), written as `FrFlowExamples` classes: rooms' three hold of the calendar's code and
    one a wrong calendar breaks fails; in Lean each follows from the claims; the theory and its obligations are the
    same without them; one setting a provided Definition's value is "checked in Scala only" (`ExamplesSuite`,
    `ExampleRunSuite`);
  - the SQLite store's stand-in checked against the model, `stored.checkedAgainst(start = …, observe = …)`, on 200
    generated runs whose bookings meet `endsAfterStart`: it agrees; one that forgets to filter by room is found at a
    call, one that forgets to add by its state; and the program run in `IO` on it lifted, as production runs it
    (`StoreModelSuite`, `ModelTests.run`, `Runs`, `Respecting`); crm's `Boundaries.lean` and `expireOnce_run`
    printed by the generator from crm's boundary, model and program, byte for byte (`CrmModulesSuite`); `impl` of
    crm's `expiryJob`, with no parts, over what `expireOnce` relies on (`ImplSuite`);
  - crm's `saveWrite` (a claim read as a call of `save`, `write` an ordinary mention) and `expiryJob` (a run from the
    world before, its post byte for byte as today's `Spec.lean`), sharing's `canViewByAccess` (four inputs) and
    `handleAnswers` (a run, `.failsChangingNothing`, and a failure clause written as a claim); a run evaluated,
    printed and initialized (`CrmClaimsSuite`, `SharingClaimsSuite`, `RunsSuite`); an unparenthesised `implies`
    chain refused at compile time;
  - the rooms model changed in place (`Changes`) with a sum matched by its derived eliminator, a record made and
    copied, a fold and a `let`, each printed and run; R7.2's helper nested in itself printing two binders with two
    names;
  - the term laws on 300 generated terms reaching every algebra, folding, splitting `implies`, one term under two
    interpreters; a vocabulary added outside the core (`count`), found by its typed key (`CountSuite`);
  - a bound variable used outside its binder fails loudly naming the binder, not with a cast error;
  - the `vocabulary` field, for a define and for a claim;
  - the first generated case a plain function breaks its post on is found, as the running service used to find it on
    a call; a program run in `IO` by the production interpreter, no call checked, `atomically` losing no update under
    concurrency, an error raised and handled; a Definition whose meaning is only a proven define wired as that
    define; a deciders list committed again after a later one removed a decider does not restore it.

  Bodies are written where they carry the design; 40 `???` in 31 files stand for ports of today's code, each with
  its step in 6.
- `r43-spike/`: the compile-time and error-message measurement of 4.13 (today's FrFlow in a copy, and the planned
  code, each with the README's rooms definitions compiled alone); and `rooms-lean/` (R12.2): the rooms module as the
  printer gives it, built by `lake` against a copy of today's `FrFlow` library, with the proofs of its four
  obligations (`Dump.lean`, `Proofs.lean`, `lake-build.log`; `LeanDump.scala.txt` is the test that wrote `Dump.lean`);
  and `rooms-lean-r14/` (revision 14): the rooms and auth modules in the owner's concepts, with the whole theory's
  obligations (consistency, the store's start, vacuity) and the examples checked against the claims, built by `lake`
  (`Dump.lean`, `AuthDump.lean`, `Proofs.lean`, `FrFlow/Witness.lean`, `lake-build.log`: fourteen theorems, none
  using `sorry`); and `rooms-lean-r15/` (revision 15): the same with `RoomBookings`, `made_inRoom`, the starts over
  `initially`, and auth's group solved in substitution order (eighteen theorems, none using `sorry`; `LeanDump.scala.txt`
  wrote `Dump.lean` and `AuthDump.lean`).
- `r43tools/budget.py`: the size budgets, measured over `r43-design`.

## 1. Summary

### The diagnosis in plain words

FrFlow is a compiler. It reads a model written in a Scala DSL, turns it into trees, checks them, and produces three
outputs: Lean files to prove, Scala functions to run and check at run time, and property tests. Around that sits a
store of the developer's decisions. The code does all of this, but it is not organised as a compiler:

1. There is no intermediate representation that the phases hand to each other. The object a user writes (`Lifted`,
   `Node`) prints itself as Lean and compiles itself to Scala on demand. What a term mentions is learned by printing it.
2. The Lean back end works on strings. Fragments carry `⟦name⟧` placeholders replaced by a regex, the open terms are
   lists of names, and three places parse printed Lean back (types, conjuncts, "doing nothing").
3. `Node` is one class for six kinds: 24 fields, 20 of them optional, edges and source positions inside it, and the
   run-time wrapper (`enforce`) and example runner attached to it. `KnowledgeBase` holds the graph, the vocabulary,
   the run-time wiring, the test settings and the violation reporter.
4. The wire format is in the core (`model` depends on `protocol`), and the ledger's rules take the 31-field wire
   record `SnapNode` as their model of a node. How code is shown correct (proven, tested, assumed) is rebuilt in the
   ledger by parsing prefixes of content strings.
5. Inside `model`, all twelve packages form one dependency cycle; every module's sub-packages form a cycle too.
   `private[frflow]` hides nothing, since every module lives in package `frflow`; `lean` and `check` use about forty
   internals of `model`.
6. Several concepts exist twice or more (a Lean type: `model.types.LeanType` and `lean.LeanType`; a test report:
   `Testing.Report` and `protocol.TestReport`; proven/tested/assumed: five places).
7. The decided content of a node is assembled from raw text: a source excerpt cut by line heuristics (which also holds
   the `idea = …` argument), a regex that strips `.under(...)`, and a fingerprint over the raw text of governed files,
   so a comment edit brings a node back.
8. `IDEA.md` is a second statement of the purpose beside the root: unstructured prose with sections that nodes name,
   decided as a pseudo-node `IDEA`, with `From: Q1, Q2` lines pointing at numbered questions of the agent layer.

### The target in plain words

1. One typed IR for the analyses, made once by elaboration: `Expr` (a term's initial form, made from it by an
   interpreter and kept beside it), `Prog` (programs over boundaries), `Statement` (what a node says, one case per
   kind), `Edge` (the DAG), `Code` (what gives a Definition its meaning), `Vocabulary`. Plain data, no printing.
2. Phases with a type at each stage: DSL → `Elaborated` → `Valid` → `Resolved` → obligations (`Prop`) → Lean AST
   (`LeanModule`) → text. A term's back ends (its Lean, its Scala value) are interpreters of the term itself, and
   obligations and programs hold the terms; only the analyses read the IR. The Lean AST says everything FrFlow generates; the printer decides
   nothing.
3. A node is `Node(id, says, statement)`: its sentence and what it says, no reason. Why it holds is the reason of its
   signed decision, shown from the ledger. Edges, code, positions and checks live in their own tables. A project's
   `README.md` is ordinary prose that FrFlow neither reads nor tracks.
4. Terms in tagless-final style: the term language is small algebras (`Sym[T]`) with interpreters (evaluation,
   the Lean printer, the IR the analyses read, folding, splitting hypotheses); binders are host functions, so no
   variable is numbered anywhere but where an interpreter binds it. One printer (`Printed`) and one evaluator
   (`Evaluate`) of terms; matching on sums, `make`, `copy`, the folds, `let`, `Either`, the list relations and a
   program's runs are algebras too. The user writes `Term[A]`, `define`, `forall` as today, in the owner's forms
   (names from the `val`, `Declaration`/`Definition`, `forall`/`always`, `implies`, a program's claim as a run from
   a world, `.refines`, `.assuming`), and never sees an interpreter.
5. No ambient state. Plain code is given its values (`implementTested(d)(env => …)`, `env(d)`); a recorded program numbers
   its steps in its own `State`.
6. Programs over boundaries are tagless: `trait Database[F[_], T[_]]`, a program `final class Job[F[_]:
   Flow](db: Database[F, Term])` whose values stay `Term`s as everywhere in a model. Lean reads the program recorded
   (`F = Recorded`); production runs it in `IO`, its adapters written over plain values (`Database[IO, Id]`).
7. FrFlow checks code before production and only then: by Lean, and by property-based tests that keep everything
   today's tests do (generated cases against the claims on each tested Definition, model-based tests of boundary
   implementations, examples as tests, shrinking, saved counterexamples, coverage of a claim's parts, the
   step-refutation search). Nothing wraps a call in production.
8. Decisions are their own pure module: one content form, an append-only ledger, review states as a fold of it, one
   rule per command, and a committed, developer-signed list of who may decide. The examples' ledgers start fresh.
9. Effects are algebras (`ProjectFiles`, `Lake`, `Git`, `LedgerStore`, `KeyRing`, the API) only where a second
   interpreter, a law suite or a capability restriction pays; the programs over them ask for `Monad`, `Parallel`,
   `Clock`. The core takes no `F`.
10. Twelve modules, each with its own top package, so `private[core]` is a real boundary; a build test checks the
   allowed package edges, the absence of cycles and the size budgets.
11. A governed file's fingerprint is over its Scala as a simple lexer reads it: comments stripped, lines and
    indentation kept.
12. The code reads one way throughout: a few patterns (4.10), each written the same way everywhere, one name per
    concept, short definitions, and comments only where the names and types do not say it.
13. The owner's core concepts (4.14), and no others: three kinds of nodes, two kinds of values (one user type each:
    `define` and `program` give a `Definition`), two quantifiers, two edges (a premise written with `.assuming`). How
    each claim is checked is derived from its formula and the meanings of what it mentions, and shown. The theory
    as a whole is proven consistent and not vacuous in Lean, with witnesses derived or searched for, and "consistency
    not proven" is a status of its own; examples are tests beside it; the world outside is said by assumptions.

### Recommendation

Rebuild FrFlow from the planned core in this repository, beside today's modules (section 6). Build the new modules
in dependency order, each with its suites; port the examples one at a time onto them, smallest first (rooms, auth,
keycloak, crm, sharing), each with a fresh ledger; delete today's modules once the last example has moved. Today's
Lean, contents and outputs are recorded once as a reference: each ported example must still have every claim proven
and every seeded bug caught, and the rooms walk-through in the README must reproduce; where the new output differs,
the difference is listed and judged, not forbidden. The owner decides each example's new ledger once, at the end,
with his key in the deciders' list.

## 2. The current architecture

### 2.1 Modules as they are

| Module | Main lines | What it holds |
|---|---|---|
| `protocol` | 758 | JSON wire types and codecs; also the ledger's domain logic (`Ledger.binding`, `forked`, `alternatives`), content hashing (`Content.hash`), `Walk`, `RunCheck`, `NodeKind`, `IdeaReview` |
| `model` | 5,153 | the DSL, the IR (`Tree`, `Steps`), the Lean printer (`LeanPrinter`, `Types`, `Names`), the evaluator (`Eval`), validation, run-time wiring and enforcement, examples, property and model tests, generators, bytecode and lambda reflection, source macros |
| `lean` | 1,340 | composing Lean files from printed fragments; obligations; reading Lean output; depends on `model`'s test fixtures |
| `ledger` | 975 | decide rules, review states, signing, key and ledger files, reports (`CodeProof`, `Proofs`, `Find`), `Idea`, `IdeaDecision` |
| `check` | 1,233 | workspace, inputs, contents, hashes, snapshot, check runner, verdict judges, lake and git processes |
| `api` | 686 | `FrFlowApi` (16 operations), `LiveApi`, view records (`Overview` 30 fields, `NodeDetails` 19) |
| `cli`, `web`, `agent` | 1,168, 167, 528 | front ends and the agent layer (conversation with numbered questions, `IdeaSources`) |

Tests: 5,176 lines across the modules; the examples' tests 1,226 lines.

### 2.2 Concepts and where each is represented

| Concept | Representations today |
|---|---|
| A domain term | `Param` (a `Term` subclass), `Subst.target`, `Printed.paramObjects/paramRefs`, `Ctx.params` (names), `ParamTerm` (wire), strings in `KnowledgeBase.onOp` |
| A type | `types.LeanType[A]` + `Shape` (model); `Types` (Lean text and Scala text printing); `lean.LeanType` (parsed back from Lean text); `TypeDecl` (both texts); `TypeText` (wire); `LeanType.known` (a global `TrieMap` registry fed by derivation, used to type boundary methods read by reflection) |
| A term / formula | `Term[A]` wrapping `Tree` (binders identified by object identity); `Lifted` (lazy tree + its Lean + its Scala); Lean text with `⟦d⟧` markers; `Content.sources` (source text) |
| A flow | `Flow[A]` (HOAS), `Steps` (first order, with `Steps.Outside` for production steps), Lean `do` text, `Flows.run` (Sync), `Flows.onModels`, `Flows.onModel` |
| A node | `Node` (24 fields), `SnapNode` (31), `Content` (JSON strings), `Reviewed`/`Review` (15), `NodeDetails` (19), `CheckedNode`, `TreeNode`, cli `NodeText` |
| An edge | `Node.declaredParents` (object refs), `Keep(invariant, Option[view], exempt string)`, `Node.replaced`, `Node.scope`; `SnapNode.parents/parts/uses/relies/covers/exempts`; `ledger.Graph.dependents` |
| Code attached | `Implementation(contract: String, factory, files with "last is the model file", wiring: String, proven, flowDef, calls)`, `ModelImpl(start, read, outside: Boolean, …)`, `RunTime`, `CodeProof` (parsed from content prefixes `"tested: "`, `"runs: "`), `Testing.testable`, `Snapshots.tested`, `Overview.contractsTested…` |
| An obligation | `Obligation(name, statement: String, description: String)`, `ObligationText` (wire), `Result`, `NodeCheck` |
| A test result | `Testing.Report/Failed/Covered/Replay` (model) and `TestReport/TestFailure/Covered/Counterexample` (protocol), converted by hand in `check.Tests` |
| A decision | `Decision` (12 fields), the ledger file format, `Decide` (command), `Standing`, `Review`, `IdeaDecision` |
| The purpose | the root node; `IDEA.md` (lead and sections), `Node.ideaSection`, `KnowledgeBase.idea`, `Content` fields `idea`, `ideaSection`, `notModelled`; `Question("Q1", …)` in the agent's conversation |

### 2.3 Data flow, end to end

```
examples/*/src: Scala vals built with the DSL (Node, Param, define, Flow, Boundary)
  │  Lifted builds Tree/Steps lazily by calling lambdas (ThreadLocal `Building`);
  │  the same object prints itself (LeanPrinter) and compiles itself (Eval)
  ▼
model.KnowledgeBase ───────────────► service/run: Wiring, Bindings (ThreadLocal), Node.enforce → production code
  │  problems: Validation (regexes over printed Lean: `∃ \(...: X\)`, inScope over type text)
  ▼
lean.Generate(kb, authored, chosen): Vocabulary, Refinement, Obligations, Evals, Coverage
  │  values are (String, Ctx); calls are `⟦d⟧` resolved by regex; idle reparses types (LeanType.nothing);
  │  restates_i reparses conjuncts (LeanText.conjuncts)
  ▼
check.Analysis(kb, workspace, Inputs): Contents (JSON of strings, source cut by line heuristics, IDEA.md sections),
  CheckHash (over Lean text), Snapshots (SnapNode), CheckRunner → lake → Verdict → NodeCheck → .frflow/checks.json;
  Tests → kb.test (model.Testing, unsafeRunSync for interleavings) → protocol.TestReport → .frflow/tests.json
  ▼
protocol.Snapshot ──► ledger.Annotate(snapshot, ledger): Graph(SnapNode), Standing, Review, Decide, CodeProof, IdeaDecision
  ▼
api.View(Annotated) → Overview, NodeDetails, Tree, Inbox → cli text, web JSON, agent
```

### 2.4 The dependency graph, measured

Details in `r43-deps.txt`. The module graph is acyclic (sbt enforces it). Inside the modules:

- `model`'s twelve packages are one strongly connected component. 2-cycles: `frflow ↔ types` (28/2 references),
  `frflow ↔ vocabulary` (22/14), `frflow ↔ term` (16/14), `frflow ↔ testing` (11/14), `boundary ↔ flow` (10/11),
  `node ↔ runtime` (7/4), `kb ↔ runtime` (8/2), `node ↔ example`, `kb ↔ testing`. The root package `frflow` (21 files,
  1,447 lines: `Eval`, `LeanPrinter`, `Steps`, `Testing`, `Trees`, `Types`) is used by and uses every other package.
- `protocol`, `lean`, `ledger`, `check`, `api`, `cli` and `agent` each have their sub-packages in one cycle.
- `model` depends on `protocol` (17 references: `NodeKind`, `RunCheck`, `RunTime`, `Walk`, `tooFew`).
- `private[frflow]` is used 171 times in `model`; since all modules are in package `frflow`, it does not stop `lean`
  and `check` from using `Binder`, `Fn.call`, `Names.*` (14), `Steps.of`, `Tree.Do`, `Types.walk`, `LeanType.ofJava`,
  `n.postFn`, `n.opType`, `.paramObjects`, `.built` and `Testing.*` (about 40 sites, listed in the appendix).
- `api` re-exports `ledger` and `check` types (`api/package.scala`), so the front ends' vocabulary is three modules'.
- `lean` depends on `model`'s test configuration (`compile->compile;test->test`), and the `check` and `lean` suites
  build their knowledge bases from `model`'s test fixtures.

### 2.5 Problems, each with where and why it hurts

The rule ids are those of `.claude/skills/scala-fp` (`references/rules.md`).

**P1. No IR between the front end and the back ends** (wrong owner, missing abstraction; B2, B3).
`vocabulary/Lifted.scala` holds a lazy `build`, `printed` (`LeanPrinter().print`) and `compiled` (`Eval.function`); its
accessors `params`, `body`, `types`, `opaques`, `paramRefs`, `defs`, `paramObjects`, `boundaries`, `errors`,
`commutes` are all read off the printed Lean. `KnowledgeBase.termsOf`, `reads`, `defs`, `types` and `Validation` get
"what a term mentions" from the printer's side effects (`Printed`). Analyses therefore depend on printing; a printer
change can change which terms a node is said to use, hence its decided content.

**P2. The Lean back end is string-typed** (illegal states, leaky layer; D5).
`lean/Vocabulary.scala` `resolve` replaces `⟦name⟧` with a regex; `Ctx` is two lists of names; `Refinement.claim`
returns `(String, Ctx)`; `lean/LeanType.scala` parses printed types back (used by `Obligations.idle` and
`Evals`); `printing/LeanText.conjuncts` cuts printed propositions at `∧` (used by `Refinement.conjunctsOf`);
`KnowledgeBase.inScope` finds type names by regex in Lean type text; `Validation.vocabulary` searches printed bodies
for `∃ (… : X)`. The Lean printer is split between `model` (`LeanPrinter`, `Types`, `Names`, `Boundary.lean`,
`TypeDecl.lean`) and `lean`.

**P3. `Node` is one class for every kind** (D1, D2, D3, D11, B2).
`node/Node.scala:14`: 24 constructor fields, 20 optional or defaulted, a hand-written `copy`. Kind is decided partly
by `kind` and partly by which options are set (`isInvariant = rule.isDefined`, `isFlow` from the operation's shape,
`kb.isStatement` from `modelOf.isEmpty`). Sentinels: `ideaSection = ""`, `file = ""`, `at = -1`. Builders reject
combinations with `require`. Edges are object references inside the node (`declaredParents`, `kept`, `replaced`,
`scope`), deduplicated by `System.identityHashCode`. The phantom `M` types nothing at run time. The same file holds
`checkExamples` (example running), `postFn` (an untyped call convention) and `enforce` (run-time checks, sampling,
assumption caching with an `AtomicReference`, reporting, throwing).

**P4. `KnowledgeBase` is a god object** (D1, B5).
`kb/KnowledgeBase.scala`: 52 members covering the graph (parents, parts, ancestors, ordered), the vocabulary (in
force, provisional, definitions used, reads), code (`implementations`, `implement`, `implementProven`, `calledBy`),
running (`service`, `run`, `definitionBindings`, `opCode`, `runtimeAssumptions`), testing (`generators`, `testing`,
`test`), examples, validation and a violation reporter (`onViolation`). Every `with…` rebuilds it by positional
constructor call.

**P5. The core depends on the wire format, and the wire format holds domain logic** (B3, M1, T9).
`model → protocol`; `protocol.decision.Ledger` contains the decision log's semantics; `protocol.Content` the hashing
rule; `RunTime.describe` and `RunCheck.describe` display text (V5). Changing a JSON field touches the core.

**P6. The ledger's model of a node is the 31-field wire record** (V2, V3, D3).
`ledger/review/Graph.scala`, `Standing.scala`, `Meaning.scala` and `Decide.scala` take `SnapNode`. `Meaning.own`
removes `.under(...)` from the `definition` text with a regex. `ledger/report/CodeProof.scala` decides proven, tested
or assumed by looking for the prefixes `"tested: "`, `"assumed, checked: "` and `"runs: "` in content strings.

**P7. Package cycles everywhere, and visibility that does not bound modules** (M1, M4; see 2.4).

**P8. Duplicate representations of one concept** (D3; see 2.2): two `LeanType`s, two test reports with a hand
conversion, five places deciding proven/tested/assumed, `Walk` in `protocol` used by `model`, the name clashes
`Term` (model, `api.details`), `Tree`/`Trees` (model, `api.report`), `Eval` (model, `lean.obligation`), `Words`
(protocol, `cli.text`), `Coverage` (model, `lean`).

**P9. Untyped core with casts** (D11).
133 `asInstanceOf` in `model`; the IR passes `Any`; `Fn.call` dispatches on arity up to nine; `Keep.brokenBy`, `postFn`,
`Wiring.service` cast the results of the developer's functions. A literal is `Tree.Lit(v: Any, …)`.

**P10. Ambient and global state in the core** (E1, E5, E6, E7).
ThreadLocals `Bindings` (values in force, also read by the evaluator), `Watch` (coverage), `Building`; the global
`LeanType.known` registry (types of boundary methods depend on which derivations ran before); `unsafeRunSync` in
`example/ExampleRuns.scala:54`; `sys.env.get("FRFLOW_SEED")` in `check/Tests.scala:34`; reflection on bytecode for
equality (`types/Adt.ownEquality`), on lambdas for parameter names and captured values, on Java generic signatures
for boundary types.

**P11. The decided content is assembled from raw text** (D5, D6).
`check/analysis/Contents.scala`: a JSON object of strings; `definition` is the node's statement cut out of its file by
indentation heuristics (`Contents.definition`), so it holds every argument written there, `idea = "…"` included;
`uses` holds Scala type text from `Types.scala` and define sources; `model` holds Lean text of the boundary model; a
flow's `implementation` holds its Lean. `check/Inputs.scala:56-72` fingerprints the raw text of every governed file
and implementation source, so removing a phrase from a doc comment in
`examples/auth/src/main/scala/auth/SessionStore.scala` put `DecisionContract` back for review (`code`).
`governs: List[String]` paths are resolved only when the checker reads the disk, and `Implementation.files` relies
on the convention that its last element is the model file (`dropRight(1)`).

**P12. Views are flattened copies** (V1, V2, V3).
`SnapNode` (31 fields), `Overview` (30 counters, 9 defaulted), `NodeDetails` (19), `Review` (15). Each is built field
by field; `Overview.of` repeats knowledge (`CodeProof`, `provenDown`) found elsewhere.

**P13. Errors are thrown from the model** (F8, F9, R1).
`require` in builders, `IllegalArgumentException` from the printer (`cannot infer the type here`), from `Types`
(function fields, redefined equality), from `Steps` (transaction inside a transaction). A model error surfaces as a
stack trace while the model loads or while Lean is printed, one at a time.

**P14. Effects are not separated into algebras** (A1, A2, X4).
`check.Disk`, `Lake`, `Git`, `JsonStore`, `KeyStore` are concrete `IO` objects; the checker's tests need Lean installed
or rebuild the workspace on disk. `LiveApi` is the only interpreter of `FrFlowApi`.

**P15. The DSL's surface is wider than its users** (S1).
`r43-features.md`: `race`, `guarantee`, `bracket`, `timeout`, `parTupled`, `ifM`, `checkedAtRunTime`, `testedWith`,
`reporting` have no use in the examples; `Boundary[T] => T` is an implicit conversion hiding an access (T6).

**P16. Behaviour is pinned only on fixtures.** `lean/GoldenSuite.scala` pins the generated Lean of two fixtures;
nothing pins the examples' Lean, contents, signatures or snapshots, which is what a refactoring must preserve.

**P17. Two statements of the purpose** (D3; the owner's call). The root says what the system is for, and so does
`IDEA.md`, as prose with sections. Nodes name sections (`idea = "…"`), contents carry the section's text, an `IDEA`
pseudo-node is decided and reviewed by section, and the agent layer links sections to questions numbered `Q1`, `Q2`
(`IdeaSources`), a numbering defined nowhere a reader of the files can see. Its own files are 98 lines
(`Idea`, `IdeaDecision`, `IdeaReview`, `IdeaSources`), plus branches in `model`, `check`, `api`, `cli` and `agent`.

### 2.6 What changed since the measurement

Between `3aa8cd7` and `e0fa3d9` (28 commits) the code gained three features the rebuild keeps, and one example:

- **`examples/rooms`** (69 lines): booking meeting rooms, a root over moments refined into a contract over start and
  end times, plain code found by binary search, nine lines of generators. The README's walk-through is written from
  its real runs; section 6 makes reproducing it a test of the rebuild.
- **A failed step refuted by a case Lean proves** (`check/proving/Refutation.scala`, 75 lines; `Testing.refute`):
  when a node's one part is a contract fixing its result (`guard ==> result === e`), a generated case where the claim
  fails with the answer `e` is searched for, and a generated Lean module proves the step false on it. The CLI says
  "the step from its parts does not hold: <case>: <what the contract answers>", and what changed since the decision
  (`whatChanged`). In the target: `testing.StepRefutation` and `proof.layout.RefutesModule`.
- **Keys count as committed** (`ledger/signing/TrustedKeys.scala`, `check/Keyring.scala`): a decision made with
  another key than the one filed under its name is refused, a filed key is never replaced, and a key file rewritten
  in the working tree verifies nothing. The owner's decision goes further: a committed, signed list of who may decide
  (4.9).
- **A contract changed under its code** (`Cause.movedUnderCode`): a generated case the unchanged code now fails is
  said as the contract's change. In the target: `decision.review.Cause.movedUnderCode`, said by the CLI.

## 3. Sources, and what this design takes from each

- **Compiler phases with typed intermediate representations.** Sarkar, Waddell and Dybvig, "A nanopass infrastructure
  for compiler education", ICFP 2004 ([program](https://icfpconference.org/archived/icfp2004/www.cs.indiana.edu/icfp04/program.html)),
  and the journal version, JFP 15(5) 2005 ([pdf](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/1E378B9B451270AF6A155FA0C21C04A3/S0956796805005605a.pdf/educational-pearl-a-nanopass-framework-for-compiler-education.pdf));
  Keep and Dybvig, "A nanopass framework for commercial compiler development", ICFP 2013, which rebuilt Chez Scheme
  this way. Taken: many small passes, each with a declared input and output language. FrFlow gets a type per stage
  (`Elaborated`, `Valid`, `Resolved`, `NodeObligations`, `LeanModule`) and one pass per change of representation.
- **Scala 3's compiler** is a list of phases over typed trees ([overall structure](https://nightly.scala-lang.org/docs/internals/overall-structure.html));
  Petrashko, Lhoták and Odersky, "Miniphases", PLDI 2017 ([paper](https://plg.uwaterloo.ca/~olhotak/pubs/pldi17b.pdf)).
  Taken: trees whose nodes carry their types (`Exprs.typeOf` is total), so passes need no environment to type a
  subterm.
- **Front end, IR, back ends.** Nystrom, *Crafting Interpreters* (2021): a front end to a tree, and several walkers of
  the same tree (resolver, interpreter). Taken: Lean printing, Scala evaluation and test generation are interpreters
  (of the terms themselves since revision 8, 4.13; of the IR for programs and obligations); the Lean printer is a
  last, decision-free walk over a Lean tree.
- **Extensible trees.** Najd and Peyton Jones, "Trees that grow", JUCS 23 (2017) ([paper](https://arxiv.org/pdf/1610.04799)):
  one AST indexed by phase. Considered and not taken: FrFlow's stages differ in what surrounds the trees (choices,
  derived relations) more than in the trees, so separate stage types around one `Expr` are simpler.
- **DSL encodings: tagless final.** Kiselyov, "Typed Tagless Final Interpreters", in *Generic and Indexed
  Programming*, LNCS 7470 (2012), pp. 130–174, the lecture notes of his course
  ([okmij.org/ftp/tagless-final/course](https://okmij.org/ftp/tagless-final/course/); the site was not reachable from
  this environment, so the notes are cited by section); Carette, Kiselyov and Shan, "Finally tagless, partially
  evaluated", JFP 19(5) 2009
  ([Cambridge](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/finally-tagless-partially-evaluated-tagless-staged-interpreters-for-simpler-typed-languages/7B2DC44A2127EBBA71ADE63809D9425F)).
  Taken (owner, revision 8; 4.13): the language as algebras over `repr` (§2.1, §3.2 `Symantics`), extension by new
  algebras (§2.2), interpreters `R` (evaluation), `S` (printing by depth) and the duplicating one (§2.3, §3.2),
  non-compositional operations by context-passing or through the initial form (§2.4, §3.3), higher-order abstract
  syntax for binders (§3.2), the partial evaluator as an interpreter transformer (CKS §4); no typechecker, since
  terms are never read back from text (§2.3). Programs over boundaries were already tagless (4.8.C).
- **Higher-order syntax without names clashing.** Axelsson and Claessen, "Using circular programs for higher-order
  syntax", ICFP 2013: binders numbered from the body. Not needed: with HOAS each interpreter names a binder by its
  depth where it binds it (LNCS 7470 §3.2's `S`), so no number is made before interpretation.
- **Algebraic design.** Chiusano and Bjarnason, *Functional Programming in Scala* (2014; 2nd ed. 2023), ch. 7–9:
  write the operations and laws first. Taken for `Gen` (a lawful `Monad`), `Declarations`, `Notes`, `Mentions`,
  `Hits`, `Tally` (monoids), `Deferred` (an applicative), the algebras of the shell with law suites.
- **Functional core, imperative shell.** Bernhardt, *Destroy All Software* ([screencast](https://www.destroyallsoftware.com/screencasts/catalog/functional-core-imperative-shell))
  and "Boundaries" (2012). **Ports and adapters**: Cockburn (2005); Seemann, "Functional architecture is Ports and
  Adapters" ([blog](https://blog.ploeh.dk/2016/03/18/functional-architecture-is-ports-and-adapters/)). Taken: every
  phase is pure; `project.program` reads inputs once through algebras, calls the phases, writes results.
- **Information hiding and deep modules.** Parnas, "On the criteria to be used in decomposing systems into modules",
  CACM 15(12), 1972 ([text](https://www.cse.sc.edu/~mgv/csce330f24/ParnasCriteria.pdf)); Ousterhout, *A Philosophy of
  Software Design* (2018). Taken: each module hides one design decision (how Lean is spelled; how Scala holds values;
  how decisions are stored) behind a small interface; the decision rules see a `Subject`, never the IR or Lean.
- **Simple made easy.** Hickey, Strange Loop 2011 ([talk](https://thestrangeloop.com/2011/simple-made-easy.html)):
  do not complect. Taken: a node's statement, its edges, its code, its position and its checks are five facts stored
  apart, each once; the purpose is stated once, by the root.
- **Types for the domain.** Wlaschin, *Domain Modeling Made Functional* (2018): make illegal states unrepresentable,
  model stages as types. Taken: `Statement`'s cases (a contract on a function and one on a flow are two cases), the
  two example shapes, `Valid` as an opaque type only `Validate` makes, `RelPath` only `parse` makes.
- **Event sourcing.** Fowler, "Event Sourcing" ([martinfowler.com/eaaDev/EventSourcing.html](https://martinfowler.com/eaaDev/EventSourcing.html));
  Young, CQRS and event sourcing ([talk transcript](https://kurrent.io/blog/transcript-of-greg-youngs-talk-at-code-on-the-beach-2014-cqrs-and-event-sourcing)).
  Taken: review states are a fold of the log over the current graph (`Standings.of`); commands (`Decide`) produce
  events (`Decision`s) or refusals; the log starts fresh with the rebuild, and a later change of an event's schema versions it,
  never rewrites the log.
- **Typelevel practice.** cats, cats-effect and discipline documentation; Volpe, *Practical FP in Scala*: algebras as
  `trait X[F[_]]`, interpreters built by `make` as `Resource`s, programs with the least capability, law suites
  against every interpreter. Taken where a second interpreter or a law exists (4.7).
- **Checking architecture in the build.** ArchUnit ([user guide](https://archunit.org/userguide/html/000_Index.html))
  is for Java bytecode; `layers-dotty-plugin` (Scala 3, version 0.0.x) and `sbt-dependency-rules-plugin` (classpath
  only) exist. Section 7 uses a small import scanner as a munit test instead, plus scalafix's built-in
  `DisableSyntax`.

## 4. The target architecture

### 4.1 Concepts, each with its theory

1. **Vocabulary** (`core.vocab`). The signature a model is written over: sorts (opaque types), declared data types,
   symbols (each a Declaration or a Definition, `ValueKind`), defines (Definitions with bodies), boundaries (operation
   signatures) and state models. Laws: each name is declared once (`Validate` reports `DeclaredTwice`); a Declaration
   is abstract and applied only where a statement is written (the types say so, `Stating`; validation finds what
   they cannot, `DeclarationInCode`); a Definition is given its meaning once, in the knowledge base or where it is
   written (`define`, `program`: `Definition.onTheSpot`; `Undefined` otherwise). Elaboration collects the vocabulary from what the terms declare (`dsl.build.Declarations`, a monoid
   that keeps two different declarations of one name for `Validate` to report), with no registry.
2. **Term** (`core.term`; 4.13). The term language as algebras over a representation `T[_]` (`Logic`, `Equality`,
   `Arith`, `Constants`, `Lists`, `Options`, `Eithers`, `Quantifiers`, `Records`, `Sums`, `Functions`, `Named`,
   `Variables`, `Worlds`, `Annotations`), bundled as `Sym[T]`; a term is `Final[A] = [T[_]] => Sym[T] => T[A]`, the
   same value for every interpreter (LNCS 7470 §2.1, §3.2). Binders take host functions (`forall(x)(p: T[A] =>
   T[Boolean])`, `lam`, `let`, a match's arms). Interpreters: `eval.term.Evaluate` (its Scala value, the only
   evaluator), `proof.lean.term.LeanTerm` (its Lean, the only printer), `ToExpr` (its IR, for the analyses),
   `Collect` (its notes), and the transformers `Hypotheses`, `PartialEval`, `Opened`, `Guarded` (each `always[T]` as
   a hypothesis), `Defining` and `Conditions` (a witness, a condition: 4.14). Laws: a written lambda run on
   arguments equals the evaluator's value, folding keeps every value, the printed Lean reads back
   (`TermLawsSuite`, `PrinterLawsSuite`). The user's `dsl.term.Term[A]` wraps a `Final[A]` and never shows `T`.
3. **Expr** (`core.expr`). A term's initial form (LNCS 7470 §2.4, §3.3), made only by `ToExpr` and kept beside the
   term (`Written(value, source, form)`): what the analyses read (the table in 4.13: the content, mentions, scope,
   the refutation's search), never printed or run. A
   simply typed lambda calculus with data, containers and quantifiers. Every node carries what its type needs
   (`Exprs.typeOf` is total); a binder's id is its level, the number of binders around it (`VarId.level`), a
   recorded program's step is numbered by the reading of the recording (`VarId.step`), so no binder captures another.
   One operator per meaning: an operator on several containers (`Contains` of a list, an option or a set) is one
   `PrimOp`, its operand's type telling which; every operation with a body (`forall`, `exists`, `filter`, `find`,
   `map`, `flatMap`) is `Expr.Iterate` with a binder, a fold `Expr.Fold`. `Mentions` (a monoid) says what an
   expression mentions.
4. **Prog** (`core.expr`). A program's steps, first order, generic in what a step holds (`Prog[Stated[?]]` for the
   back ends, `Prog[Expr]` by `Progs.map` for the analyses): the free monad over the boundaries' operations and the
   models' state, with errors, loops and concurrent steps (`Par`, `ParEach`, `Race`, `Guard`, `Atomic`), each
   concurrent step holding its branches and, where it needs one, its sequential reading (`Progs.sequential`). It is
   what the recording of a program gives (`dsl.flow.ReadRecording`). Meanings: a Lean `do` block, a run on the models
   and a run on the adapters (`eval.flow.FlowInterpreter` over a `World`).
5. **Statement and Node** (`core.spec`). `Node(id, says, statement)`: no reason, which is its decision's. `Statement`
   has three cases (owner §15): `Claim(formula, reliance)`, `Assumption(formula)` and `Design(governs)`; no kind of
   contract, invariant, model or definition, under any name. What a statement ranges over is read off its formula
   (`Range`: `Possible` for `forall`, `Made(ty)` for `always[T]`, `Reached(models)` for `always(stored)`); where a
   claim applies one Definition to exactly its leading variables, it reads as a call of it (`CallForms`, derived:
   `CallForm.Call(op, post)` or `Run(op, post, failure)`). A claim constrains every Declaration and Definition it
   mentions (`Constrained`). One idea per statement is a style guide (§10, §16), not checked. Examples are not part of
   any node: `core.example.Example(name, givens, fact)` is a closed fact checked beside the knowledge base. `kind`,
   `range`, `call`, `outside` and `exprs` are functions of the case.
6. **Refinement** (`core.graph`). The DAG: nodes in the model's order and `Edge`s (`PartOf`, `Assumes`,
   `Replaces`). The root statements are the claims without parents, on any Definitions and Declarations, a statement
   relating several among them (owner §11, which replaces the one-root law: a knowledge base has a small set of them,
   rooms' booking's two claims and its two claims of `always`; keeping it concise is the author's job, which the
   agent's skill says, and no `SeveralRoots` problem is raised). Laws, made true by `Validate`: at least one root
   statement (`NoRoot`), an assumption never one; acyclic, every edge inside the graph; a premise (`.assuming`, the one
   mechanism for one) is an assumption or a claim of `always` (`PremiseNotAssumed`); a fact about the outside is never
   a part (`OutsideAsPart`) and only an assumption says one (`OutsideClaimed`); a claim's `.assuming` lists exactly the
   facts about the outside its check rests on (`PremiseMissing`, `PremiseNotNeeded`; `WriterNotListed`); a node with
   proven code has as parts only claims about what its code calls (`PartNotCalled`).
7. **Scope** (`core.analysis.Scope`, `Guards`, `Premises`). Where an `always` applies, derived: of `always[T]`,
   the Definitions whose result can hold a `T` (read off `Ty` and `DataType.fieldTypes`: where a value is made) and
   the programs writing a store whose state can; of `always(stored)`, the programs writing the store, once per
   program. `Guards` gives each `always` its hypothesis on a variable of a type: the rule of each value, each element
   of a list of them, each one a record's field holds, and each world's state it is about. The makers of an
   `always[T]` are the proven defines and the store operations whose result it applies to (`Scope.modelMakers`).
   `Premises` derives which facts about the outside each check rests on, to check the `.assuming` lists (4.14). A
   claim mentions only what it constrains, so nothing is exempt.
8. **Code** (`core.code`). What gives a Definition its meaning (owner §15): `Proven` (a define), `ProvenFlow` (a
   recorded program), `Tested` (plain Scala, with the Definitions it calls), `Valued` (a value fixed in the model) or
   `Provided` (a value given where the code runs), written `implementProven`, `implementTested`, `implementValue`,
   `implementProvided`, or carried by a `define` or `program`, one per Definition (`CodeTable`), and the implementations run
   against a model (`CodeTable.realized`, keyed by the `behavesAs` assumption). Plain code is a handle `Impl(arity,
   make: Values => AnyRef)`: it is built from the values it is given (`Values`, explicit). How each claim is checked
   is one function, `core.checking.Checking.of` (its lines derived, never written), and how each piece of code is
   shown, `Shown.of`: `Shown(proven, tested, assumed)`.
9. **Resolution** (`core.analysis`). `Validate` makes a `Valid` model or returns every `Problem`; `Resolve` computes
   once what each node uses, calls and rests on (`relied`). There is no choice of the definitions in force: a
   Definition has one meaning, given once.
10. **Obligation** (`proof.obligation`, `proof.terms`, `proof.whole`). What Lean is asked, as a proposition in the
    logic of refinement: claims and conjuncts applied to their open terms, `Implies` with named hypotheses, `Iff`,
    `Both`, `Not`, `False`, commutation, `Forall(about, body)`/`Exists`, `ForEvery`/`ForSome` with named binders,
    `Starts` and `Inhabited`. `TermTable` (computed once per analysis) says what each declaration is applied to. The
    required set and the tries are today's, less `check`, each made with the sentence its Lean is documented with; a
    refuted step adds its `Refutes` module. A node whose code is proven (a define, or a program, whose run on the
    models `f_run` stands for the Definition) is proven by `impl`, "∀ U, H → claim[d := code]", `H` its parts (each a
    claim about what the code calls; the boundaries' models are in `f_run` itself) or, with no parts (a leaf, as
    crm's `expiryJob`), what the code relies on: the claims on the Definitions it calls, through the defines it
    calls, wherever they sit (`Resolved.reliesOn`, less a callee left open above whose word the node names);
    `complete` is not asked of it (`Required`, `Callees`; `BookSuite`, `ImplSuite`). What always holds: every
    statement's variables come with each `always[T]`'s hypothesis (`Guarded`), and each program writing a store is
    asked, for each `always` about the store's state or a type it holds, `cover_<op>`: "∀ U, H → A.keeps_op[op :=
    f_run]", every run from a world meeting every `always`, on inputs meeting theirs, ends in one meeting A
    (`Prop.Keeps`, `Keeping`); and `made_<maker>` of each `always[T]`, every result of a proven define or a store
    operation on its model meets it (`Prop.Makes`, `Making`; 4.14). The theory as a whole (4.14, `proof.whole`): `consistent_<i>` per group and
    `start_<node>` per `always` about a store (`Joint`), `inhabited_<node>` and `satisfiable_<i>_<node>`
    (`Possible`), each with the witnesses derived or found (`Discharge.Witnessed`, else `Unwitnessed`: stated only),
    and `example_<i>` per example (`ExampleGoals`, a try).
11. **Lean** (`proof.lean`, `proof.layout`, `proof.reading`, `proof.verdict`). A Lean AST able to say everything FrFlow
    generates; `lean.term` prints every term from its final form (`LeanTerm`, the scope and the naming passed down; a
    define's body once, as its `def`; `Printed` the entry points); `lean.lower` gives only the structure around terms
    its Lean: a `Prog`'s `do` block (`LowerProg`, its variables named in `State[Naming, _]`), each `Prop` its
    statement (`LowerProp`, a `Writer` of the open terms met), each obligation its declaration (`LowerObligation`),
    and a constant its literal (`LowerValue`); `Print` is a fold that
    decides nothing; the proof-file rules and the judges are pure functions returning cases.
12. **Testing** (`testing`, over `eval`). Code checked against what is decided before production, by generated
    cases: tested Scala against every claim mentioning its Definition (`PropertyTests`: each case's inputs drawn, the
    values its code reads made by `eval.run.Wiring`, the call judged by `eval.run.CallCheck` where the claim reads as
    a call, else the claim evaluated whole on its drawn variables; a statement with no Scala value not checked
    (`checking.Evaluable`); the first failing case kept to replay), an
    implementation of a boundary against its model (`ModelTests.run` of `stored.checkedAgainst(start = …, observe =
    …)`: generated runs of the boundary's operations, `Runs`, on both, compared call by call and then by the state
    each holds), a concurrent program's interleavings on the adapters (`Interleavings`), and a failed step's refuting
    case (`StepRefutation`); the witnesses of vacuity searched for (`search.Witnesses`: the generators' first values,
    then the small values of each type, `Small`, each judged by the evaluator). Every value drawn by its type meets
    each `always[T]` of the type (`Respecting`). Law: a run is a function of its seed and the developer's code.
13. **Decision** (`decision`). `Content` (named fields of three shapes, a canonical print, `hash` and `ref`), one form;
    `Chain`; `CodeFingerprint`; `Decision`; `Ledger` (append-only); `Payload` and `Seals` (signing, pure once the key
    is read); `Deciders` (who may decide: committed, signed, each version by a key of the version before);
    `Standings` (the fold, with rewording); `Decide(reading, command, author)` (one rule per `Command`). It reads
    `Subject`s only.
14. **Shell** (`project`, `api`, `wire`). Algebras over `F[_]` where they pay (4.7), programs over them, the `Analysis`
    value (every pure phase computed once from the inputs), the API whose views are functions of a derived `View`,
    and the export formats.
15. **Consistency and vacuity** (`core.consistency`; 4.14). A theory's statements have a model: the bottom statements
    and the assumptions beside them, grouped while they share an open value (a Declaration, or a Definition no proof
    or fixed value gives a meaning), each group satisfiable for every value provided (`consistent_<i>`), each
    `always` about a store met at its start (`start_<node>`); and they are not vacuous: each `always[T]` admits a
    value, each condition `A` of `A implies B` can hold. Witnesses are derived from the formulas (`Equations`,
    `Defining`; a bound; proven code) or found by a search; a group without one is "consistency not proven", a status
    and not a failure. The contradiction search stays an early refuter only.

The part of FrFlow a production system links against is the DSL and `eval`: terms, the recorded and the running
interpreters of programs (`Recording`, `eval.Running`), `d.fn(env)` and `knowledge.code(d)(…)`. It has no ambient
state. Its state is one memo in an immutable value (`KnowledgeBase.elaborated`, a `lazy val`) and, in a running
program, the one lock its transactions take (`Running`'s `Mutex`). A define is run by the evaluator on its term
(`d.fn` is `Evaluate` over the define, curried), so nothing is compiled and kept (`Def.compiled` and `Once` are gone).

### 4.2 Phases and their types

| Phase | From | To | Module | Effects |
|---|---|---|---|---|
| construct (the user's vals) | Scala | `dsl.node.Node` (head + `Deferred[Statement]`), `Term` (a final term), `Declaration`, `Definition` (a `define` or `program` among them, carrying its meaning: `OnTheSpot`), `Boundary[B]`, `KnowledgeBase`, `FrFlowExamples` | `dsl` | none; nothing runs; nothing numbered |
| elaborate | `KnowledgeBase` | `ValidatedNec[ElabError, Elaborated]` | `dsl.kb.Elaborate` | calls the user's lambdas once on their inputs' variables, keeps each term with its IR (`Written`, by `ToExpr`), records each program over `Recorded` and reads it (`ReadRecording`, its own `State`) |
| validate | `Elaborated` | `ValidatedNec[Problem, Valid]` | `core.analysis.Validate` | pure |
| resolve | `Valid` | `Resolved` | `core.analysis.Resolve` | pure |
| run Scala | `Resolved`, `Semantics`, the examples | `Computed`: each example on the code (`OnCode`), the witnesses found for vacuity | `project.program.RunScala` over `eval.run.ExampleRun` and `testing.search.Witnesses` | `F: Sync` (the developer's code runs; programs run on the models) |
| obligations | `Resolved`, authored set, the witnesses found, the examples | `List[NodeObligations]`; the whole theory's `List[Obligation]` | `proof.obligation.Obligations`; `proof.whole.Joint`, `Possible`, `ExampleGoals` | pure |
| lower and lay out | `Resolved`, obligations, `TermTable` | `List[LeanModule]` (with `Whole.lean`) | `proof.lean`, `proof.layout.LeanProject`, `WholeModule`, `LowerWitness` | pure |
| print | `LeanModule` | `String` | `proof.lean.print.Print` | pure |
| prove | modules | `ProverRun`s → `Judged` → `NodeCheck` | `project.program.NodeChecker` over `Lake` | `F` |
| test | `Theory`, `Semantics`, `Plan`, `Draw` | `Option[TestReport]`, a refuting case | `testing.PropertyTests`, `ModelTests`, `Interleavings`, `StepRefutation` | pure given a seed (the developer's code aside); `Interleavings` needs `Async` |
| project | `Resolved`, checks, tests, sources | `Content` per node, `Subjects` | `project.pipeline.Contents`, `ReadSubjects` | pure |
| review | `Subjects`, `Ledger` | `Map[NodeId, Standing]` | `decision.review.Standings` | pure |
| decide | `Reading`, `Command`, `Authorship`, the committed `Deciders` | `Either[Refusal, Ledger]` | `decision.rules.Decide` | pure; the decider checked, then signed and stored, by `DecideProgram` |
| export | `Analysis` | `wire.snapshot.Snapshot`, `checks.json`, `tests.json`, ledger file | `wire` | codecs only |
| view | `Analysis`, warnings | `View`; `Views.overview/beside/tree/inbox` | `api.view`, `api.node` | pure |

Outside the pipeline, in the developer's production code: a program runs in `F: Async` over `eval.Running` with its
adapters lifted (`database.lifted(adapter, running)`), and plain code is built with `knowledge.code(d)(bindings*)`.
Nothing there checks a call.

`project.pipeline.Analysis(valid, inputs, computed)` holds the stages after validation as lazy values (`decided`,
`provisional`, `obligations`, `modules`, `subjects`, `standings`), so an operation computes only what it reads and each
stage once. It holds the model once (`Valid` wraps the `Elaborated`).

### 4.3 Modules and the direction of dependencies

```
   core ◄── dsl ◄── eval ◄── testing        (facade `frflow.*` in eval: the DSL, programs, `env(d)`, `d.fn`, `code`)
    ▲  ▲
    │  └── proof
    └───── decision
   wire ─► proof, decision, testing (the export formats)
   project ─► proof, testing, decision, wire        (the shell: algebras, programs, analysis)
   api ─► project ;  cli, web ─► api ;  agent ─► cli, web
```

| Module | Top package | Depends on | Holds |
|---|---|---|---|
| `core` | `frflow.core` | cats-core | names, `Ty`, the term algebras and the interpreters every back end shares (`term`: `Sym`, `ToExpr`, `Collect`, `PartialEval`, `Hypotheses`, `Opened`, `Guarded`), `Expr`, `Prog`, `Value`, vocabulary, statements (three kinds), examples, `Gen` (data), edges, code (`Impl`, `Values`), `Theory`, `Elaborated`, `analysis` (with the outside's premises), `checking` (how a claim is checked), `consistency` (groups, witnesses, vacuity) |
| `dsl` | `frflow.dsl` | core | the surface syntax and elaboration (`build`, `term`, `vocab`: `Declaration`, `Definition` and `OnTheSpot`, `DefinitionSyntax`, `Stating`, `Opaque`; `shape`, `node` (three forms, `always`, the outside's formulas), `flow`, `model`, `kb`, `example`); the closed `Term[A]`; the `Flow` capability, `Recorded` and its reading, `Boundary`, `Clock`; `model`: `Model`, `ModelState`, `StoreModel`, `AdapterCheck`; source and derivation macros |
| `proof` | `frflow.proof` | core | obligations, open terms, Lean AST, the Lean printer of terms (`lean.term`, the only one), lowering of the structure around terms (programs' blocks, propositions, declarations, constants), printing, layout (`RefutesModule`, `WholeModule` included), the whole theory's obligations (`whole`: consistency, vacuity, examples) and their witnesses (`LowerWitness`), proof-file rules and Lean's output, judges |
| `eval` | `frflow.eval` (+ the facade `frflow`) | dsl, cats-effect-kernel, cats-effect-std | the evaluator of terms (`term.Evaluate`, the only one), `Semantics` (a formula, a written lambda, a constant, each by `Evaluate`), `Env`, `Literals`/`Reflect`, `Fn` (casts), `term.DefSyntax` (`d.fn(env)`), `CodeSyntax` (`knowledge.code`), `Running` (production's `Flow`); `run`: `CallCheck` (`Made`: each `always[T]` of a call's values), `Assumes`, `Wiring`, `ExampleRun`, `OnCode`; `flow`: `FlowInterpreter` over a `World`, `FlowError` |
| `testing` | `frflow.testing`, `frflow.testing.report` | eval, cats-effect | `Draw`, `Respecting`, `Case`, `PropertyTests`, `ModelTests`, `Runs`, `Difference`, `Interleavings`; `search`: `Small`, `Witnesses`, `StepRefutation`; `report`: `TestReport`, `Failure`, `Against`, `Hits`, `Position`, `Made` |
| `decision` | `frflow.decision` | core (names, `graph.Walk` only) | content, ledger (with `Deciders`), signing payload, review, rules |
| `wire` | `frflow.wire` | proof, decision, testing, circe | the snapshot by kind; the codecs of the ledger file, the deciders' list, checks and tests |
| `project` | `frflow.project` | proof, testing, decision, wire, cats-effect, fs2 | algebras and interpreters, programs, `Analysis`, contents and subjects, code fingerprints, configuration |
| `api` | `frflow.api` | project | `Reading`, `Deciding`, `Proving`, `FrFlowApi`, the view (`api.view`) and the node views (`api.node`) |
| `cli`, `web`, `agent` | `frflow.cli`, `frflow.web`, `frflow.agent` | api (agent: also cli, web) | front ends and the agent layer |

Twelve modules: the thirteen of revision 6 less `runtime` (owner E and "no run-time checking"). The planned code has
the first nine; `cli`, `web` and `agent` keep their structure and are rebuilt on the new API (section 6).

**Plain code and programs, without ambient state.**

- Plain code is given its values. `kb.implementTested(admit)(env => SessionStore(env(grants), env(sessions)).decide)`
  attaches an `Impl` whose `make` takes a `core.code.Values`; `env(d)` (`dsl.kb.ValuesSyntax`) reads one, typed by
  its Definition (a Declaration has no value to read). Whoever runs the code makes the values: an example
  (`ExampleRun`, its `:=` bindings over `Wiring`), a test (`Wiring` over the values drawn), production
  (`knowledge.code(d)(bindings*)`, the same `Wiring` over the bindings given).
- `d.fn(env)` is `eval.term.DefSyntax`: the define's body run by the evaluator (`Evaluate`) on the arguments, its
  symbols read from `env`; nothing compiled or kept.
- Terms are final (4.13): a binder's body is a host function, and each interpreter names its variable where it binds
  it. Elaboration calls a lambda once on its inputs' variables, bound at levels `0 … n-1` (`DefineShape.binder`), and
  keeps the term with its IR (`Written.formula`, `Written.lambda`, `Written.steps`); `Source.of` reads only the lambda's text and its
  parameters' names (`AsWritten(text, params)`), hints for printing.
- A program over boundaries is a class over its effect: `final class Expiry[F[_]: Flow](db: Database[F, Term])`. Its
  values are `Term`s; `Flow[F]` (a `Monad` with `cond`, `each`, `raise`, `handle`, `guarantee`, `race`, `parTupled`,
  `atomically`, and `ifM`, `bracket`, `timeout` made of them) is all it may do besides calling its boundaries.
  - For Lean, `program { (now: Term[BigInt]) => Expiry(database.recording).run(now) }` records it with
    `Recording`'s `Flow[Recorded]` and the boundary's recording instance; `ReadRecording` reads the recording into
    `Prog[Stated[?]]`, numbering each step's result in its own `State` (`VarId.step`); the define's form is those
    steps (`Form.Steps`), its IR `Expr.Do` over `Progs.map` of them.
  - In production, `Running.make[IO](env)` gives `Flow[IO]` (a condition's term evaluated by `Evaluate`,
    each result a term of its value again, `atomically` under one `Mutex`), and `database.lifted(adapter, running)`
    turns the developer's `Database[IO, Id]` adapter into the program's `Database[IO, Term]`.
  - In Scala tests and examples, the recorded `Prog` runs in `eval.flow.FlowInterpreter` against a `World`: the models
    (flow examples; the model each implementation is tested against) or the adapters (interleavings, by
    `BoundaryOps.call`).

**Checking code before production, one job per function.** Today's `Node.enforce` checked each call where code runs,
and `Node.checkExamples` ran the examples. Both now run before production only, and share the call check:

- `eval.run.CallCheck.of(semantics, theory, node)`: what one call is checked against, built once: the post (the
  Definition given the call's result for its inputs, as a claim read as a call needs) and each `always[T]` of the
  call's values (`Made`: each input and the result, each element of a list of them); `broken(call, env):
  Option[Broken]`.
- `eval.run.Wiring(semantics, theory)` (what `service`'s wiring was): the values a call reads, made explicitly: the
  defines (each computed by its term), the meanings of the Definitions it may call (tested Scala, a fixed value, an
  adapter), and the values given, which win; `needed(node)` is what a test must still draw (what the claim reads,
  what the code calls).
- `eval.run.ExampleRun`: each example's fact evaluated with every Definition given its meaning (`OnCode.Holds`,
  `Fails`, `NotEvaluated`, or `Abstract` when it is about a Declaration); against the claims it is Lean's
  (`example_<i>`).
- `testing.PropertyTests` (what `service`'s check of a call was): each generated case judged by `CallCheck` over the
  values `Wiring` makes; the first failing case shrunk, saved, and replayed first. An outside system's adapter (crm's
  `recordsByQuery`, keycloak's `sessionLookup`) is tested this way against its assumption's formula, and against its
  model by `ModelTests` (generated runs on the adapter and the model, compared call by call).

State, each piece named: `KnowledgeBase.elaborated` (a `lazy val`), `Running`'s lock, and the `State` of a
recording's reading. The architecture test (7) allows atomics and locks only in `eval.Running` and the interleavings'
run (`FlowInterpreter.concurrent`), and no `ThreadLocal` anywhere. The casts are listed in 4.11; the interpreters of
terms have none, and the term language one (`Term.bound`, 4.13).

Serialization points outward: `wire` depends on the domain and nothing but the shell depends on `wire`. The front
ends see `api.view` and `api.node` values only. Production code depends on `eval` (and through it `dsl`, `core`) and
never on Lean, the ledger, the tests or the CLI.

### 4.4 How a node is represented

Planned code: `src/core/frflow/core/spec/`, `example/`, `code/`; the DSL surface in `src/dsl/frflow/dsl/node/` and
`shape/`. Every field of today's `Node` has a place:

| Today (`node/Node.scala`) | Target | Rule |
|---|---|---|
| `id` | `spec.Node.id: NodeId`, the val's name as written (`Source.valName`) | renaming the val renames the node; one name in code, reports and Lean (R12.1) |
| `statement` | `Node.says: String` | |
| `why` | deleted (owner): the reason is the signed decision's, `Decision.reason`, shown as `Says.reason` | |
| `kind` | the `Statement` case, one of three: `Claim`, `Assumption`, `Design`; `Statement.kind` | owner §15 |
| `declaredParents` | `Edge.PartOf` in `Theory.edges` | edges in the graph |
| `formula` | `Claim.formula`, `Assumption.formula: Written[Expr]` | |
| `post` | derived where the formula reads as a call: `CallForms.of(claim)`, `CallForm.Call(op, post)` or `Run(op, post, failure)` | owner §15 |
| `local` (`checkedBy`) | deleted with run-time checking | |
| `op` | derived: the Definition a claim reads as a call of (`CallForm.op`); a claim constrains every value it mentions (`Constrained.of`) | owner §14, §15 |
| `rule`, `scope` | the formula: `always[T](x => …)` (`Range.Made`) or `always(stored)(s => …)` (`Range.Reached`), its rule a define named as the node; where it applies, derived (`Scope`); today's relation of answers (crm's `noCrossTenantRead`) is a claim `forall` over the Definitions it relates | owner §13, §15 |
| `substs` | a claim of one equation (`authorized(u, p) === grants.exists(…)`), or a `define`; a value fixed in the model is `implementValue(d)(v)` | owner §15 |
| `cases` | not on a node: an example is a test beside the knowledge base, `class GrantedExamples extends FrFlowExamples(rooms): example(name, d := v): fact` (`core.example.Example`, a closed fact) | owner §18, R14.4 |
| `governs: List[String]` | `Design.governs: NonEmptyList[RelPath]` | D4, D6 |
| `kept` (`Keep` with `Option` view and string) | deleted: who keeps an `always` is derived (`Scope`), and a claim mentions only what it constrains, so nothing is exempt | owner §15 |
| `ideaSection = ""` | deleted (P17) | |
| `file = ""`, `at = -1` | `Sited(node, at: Span)` in `Theory.nodes` | D5 |
| `expected` | a claim the expecting claim refines: `.refines(consequence)` | owner §15 |
| `replaced` | `Edge.Replaces` | |
| `modelOf` | the model, `val stored = store.model("…")(Stored(_))` (`StoreModel`: the state, read as `stored.in(before)`, and `Stored`, an instance of the boundary's trait over it), and an assumption about the outside, `Node.assumption("…")(store.behavesAs(stored))` (`OutsideFact.BehavesAs`); a premise written `.assuming(storeModel)` by each claim resting on it, the list checked (`Premises`), never a part; adapters checked by `stored.checkedAgainst(start = …, observe = …)` | owner §16, R12.1 |
| `runCheck` | deleted with run-time checking | |
| `openAbove: Boolean` | `Claim.reliance: Reliance` | D8 |
| `failure` | part of the formula: the run's `.failing { … }` side or `.failsChangingNothing[E]`, read as `CallForm.Run.failure` | D1, D2 |
| `[M]` | none: a DSL node is `Node(head, Deferred[Statement])`; what a claim is about is typed by its Definitions | owner §15 |
| `parents`, `isInvariant`, `shownKind`, `isFlow`, `opType`, `defines`, `referenced` | `Refinement.parents`, `Range`, the CLI's renderer, the call form, the Definition's `Ty`, the defines it mentions, `Exprs.mentions` | D3, V5 |
| `under` (now `refines`), `replaces`, `assuming` (new), `exempt`, `keeps`, `examples`, `leftOpenAbove`, `failsChangingNothing`, `onFailure` (now the run's `.failing`), `expects` | `NodeSyntax` on `Node`: `.refines`, `.assuming`, `.replaces`, `.leftOpenAbove` (a claim's only: `Fault.NotAClaim`); `exempt`, `keeps`, `examples` and `expects` deleted; the failure clause is in the formula | S2 |
| `checkExamples`, `postFn`, `broken` | `eval.run.ExampleRun`, `CallCheck` | B2 |
| `enforce` | deleted: the call check it made is `testing.PropertyTests` over `CallCheck` and `Wiring`, before production | B2, F1 |

The surface is not a mirror of the core: a DSL node is `Node(head: Head, statement: Deferred[Statement])`, the head
holding what every node has as written (id, sentence, position, links), and the statement built when elaborated.
There are three forms and no fourth: `Node.claim(statement)(formula)`, `Node.assumption(statement)(formula)` and
`Node.design(statement)(paths*)`. They take no reason and no id: the id is the val's name as written (`val
grantWhenFree = Node.claim(…)` is `grantWhenFree`, read at compile time by `Source.valName`), the one name the node
has in code, in reports and in Lean's namespaces (R12.1); renaming the val renames the node, which reviews it again as
any changed id does. A formula is a context function, `Stating ?=> Term[Boolean]`: only there (and in an example)
may a Declaration be applied (4.14). `Node.contract`, `Node.invariant` and `Node.definition` do not exist
(`FormsSuite`). Where a claim applies one Definition to exactly its leading `forall` variables (alone, or one side of
its equation), `CallForms` reads it as a call of it: the `Opened` interpreter turns the formula into the post over
the call's inputs (and, for a program, its result and the worlds), the post a call of tested Scala is checked
against; another Definition applied to the same variables is an ordinary mention. Nothing is refused for not reading
as a call: such a claim is checked as a whole. Links are `.refines(parent)` (was `.under`) and `.assuming(premise)`,
an assumption or a claim of `always` the node's proof assumes (`Edge.Assumes`: never a part, so `parts`, `impl`,
`PartNotCalled` and the view's `Part` leave it out). The facts about the outside a check rests on are written there
too, the one mechanism (R14.3): `Premises` derives what each check needs and refuses a list that misses one or names
one not needed; `show` lists each with what it is a premise of.

What always holds is stated once, as a claim of `always` (owner §13, §15; no statement glues ideas with `&&`, a
style guide only): `Node.claim("Every booking ends after it starts.")(always[Booking](b => b.start < b.end))` and
`Node.claim("The bookings held never overlap.")(always(stored)(held => held.pairwise(apart)))` (`AlwaysSyntax`).
The rule becomes a define named as the node (`Defines.define`), declared in the vocabulary. Lean assumes each
`always[T]` as a hypothesis on every variable of `T` a statement is about (`Guarded`, 4.13), asks each program
writing the store to keep each `always` about its state (`cover_<op>`, `Keeping`), and the state the store starts in
to meet it (`start_<node>`). An `always[T]` is also checked where a tested Definition makes a value (`Made`, in
`CallCheck`; `Broken.Always`) and met by every generated value (`testing.Respecting`).
`define { (a: Term[A]) => … }` makes a `Definition[A => R]` (and `define { (a, b) => … }` a `Definition[(A, B) =>
R]`, to six inputs) carrying its meaning (`OnTheSpot`: `Code.Proven`, its written lambda, and its `core.term.Body`,
whose body is a `lam` per input, 4.13)
named as its val (`Source.valName`, read at compile time) from the define's `DefineShape` (a lambda over the inputs
only, making no statement): a `Definition` whose body is the lambda in final form, called by name in other terms
(`covers(b, t)`, or passed as a function: `held.pairwise(apart)`); `program { (a: Term[A]) => … }` makes a
`Definition[A => Program[R]]` whose meaning is the recorded program's steps (`Code.ProvenFlow`). A lambda's parameter names come from its tree at compile
time (`Source.of`), as hints for printing; no variable is numbered (4.13).

**An error waiting for its place.** The front end has one shape for a part of a model built later, `Deferred[A]`
(errors accumulate, declarations merge), and one for an error found before its place is known: a `Fault` (an enum
with no site). Terms carry faults (`Notes.faults`), constants that are not data give one (`Reify`, `Lift`), and a
lambda that cannot return a term throws a `Failure(fault)`. `Elab` places them once at the part's `Site` (a node, or
a define): `ElabError(at: Site, fault: Fault)`.

### 4.5 Views are derived, and the API

- `api.view.View(nodes: List[NodeView], roots, whole, overview, warnings)` is derived once from the analysis
  (`Views.of`); the front ends see it and never `Analysis`. `whole: WholeView` is the theory as a whole (4.14): each
  consistency group (`GroupView`: its statements, the witness of each open value, `GroupStatus.Proven`,
  `Evidence` or `NotProven`), what is shown possible (each `always[T]` and condition, with Lean's status), and the
  examples (`ExampleView`: on the claims, on the code).
- `api.node.NodeView(id, says, place, proof, code, review)` replaces `NodeDetails` (19 fields) and the view's half of
  `SnapNode` (31), one group per concept, each made by one function of `api.node.NodeViews`:

| Group | Fields | Replaces |
|---|---|---|
| `Says` | `kind`, `statement`, `written` (the formula as written), `checking` (how it is checked, in words, derived: `Checking`), `mentions`, `reason` (the binding decision's, from the ledger) | `node`'s texts with `why`, `terms`, `defs` |
| `Placement` | `root`, `related: List[(Relation, NodeId)]`, `apply(relation)` | `isRoot`, `parents`, `parts`, `designs`, `definitions`, `usedBy`, `calls`, `calledBy`, `keptBy`, `rivals` (one list each); `beside`, `above` are functions of the view (`Views.beside`) |
| `ProofView` | `status`, `results`, `findings`, `authored` | `status`, `obligations`, `messages`, `proof` (the examples are the theory's, `WholeView`) |
| `CodeView` | `shown: Shown`, `report` | `codeProof`, `trusted`, `tested`, `implementationProof` (`runtime` deleted) |
| `ReviewView` | `standing`, `decision`, `waitsFor`, `notMechanical` | `Reviewed`'s state, causes, decision, wait |

- `Overview` is fields of `Tally[K]` (a commutative monoid) by concept, the consistency groups by `GroupStatus` and
  the examples among them; `Views.overview` is one `foldMap` each. `status` warns of each group not proven
  (`Warning.ConsistencyNotProven`).
- `tree` and `inbox` are functions of `View` in `Views`.
- The snapshot (`.frflow/kb.json`, DAG §4) is rows of `wire`'s own: `Snapshot(kb, roots, trusted, vocabulary, nodes,
  consistency, examples)`, each `SnapNode(header, place, check, body)`: the `Header` (id, kind, hash, content), the
  `PlaceRow` (parents, parts, uses, relies, covers), the `CheckRow` (status, `holds`, each obligation with its
  statement) and a `Body` by kind (`Stated`, for a claim or an assumption: how it is checked, its call form, its
  code and its tests; `Design`, the paths it governs); `GroupRow` and `ExampleRow` beside the nodes. `wire.snapshot.Rows` is the one mapping from domain values, so
  the codecs are in the rows' companions (no orphan instances) and a domain change reaches the export only through
  `Rows`. Today's per-node `split` is not repeated: it is the split's obligations' statuses. The front ends' `--json`
  prints these rows; the `api.node` views are never encoded. It is an export for tools; no FrFlow module reads it
  back.
- The API is three algebras, held together by `FrFlowApi[F](reading, deciding, proving)`:

| Algebra | Operations | Today's |
|---|---|---|
| `Reading` | `view`, `diff(node)` (field diffs and the governed code's `git diff` since the decision's commit), `find(words)`, `modelFingerprint` (the web view's stale-model guard) | `tree`, `show`, `inbox`, `diff`, `find`, `modelFingerprint` |
| `Deciding` | `developer(as)`, `preview(command, by)`, `decide(command, by)` | `decide`, `preview`, the developer's name |
| `Proving` | `render`, `status` (writes the snapshot, returns the view), `check(only): Stream[F, CheckEvent]`, `ci: Stream[F, CheckEvent]`, `scaffold(node)` | `render`, `status`, `check(…, progress)`, `ci(progress)`, `scaffold` |

### 4.6 Error model

| Where | Type | Channel |
|---|---|---|
| elaboration | `ElabError(at: Site, fault: Fault)`; `Fault`: `DeclaredLater`, `NoType`, `FunctionEquality`, `NotData`, `NoField` (a field the record's derived selectors lack), `BadPath`, `NotAClaim` (`.leftOpenAbove` on an assumption), `OutsideStep`, `NotATerm` (a program's step gave a value that is not a term), `ProgramMentioned` (a program given on the spot named in a statement: claims speak of the Definition it is the meaning of), `NotProvenCode` (`implementProven` given a Definition that is no define or program), `MeantWhereWritten` (a meaning given to a Definition `define` or `program` already gave one), `Thrown`; a Declaration in code, a contract, an invariant, a definition node, `Def1` or `Steps` does not compile (`Stating`, and no such form) | `ValidatedNec`, all collected; faults travel unplaced on terms and in `Failure` until `Elab` places them |
| structure | `analysis.Problem` (cases with data; `NoRoot` (`SeveralRoots` is gone, owner §11); `PremiseNotAssumed`, a premise that is neither an assumption nor a claim of `always`; `OutsideAsPart`, a fact about the outside refining a node; `OutsideClaimed`, a claim saying one; `PremiseMissing(id, needs, by)`, a fact a check rests on that the claim's `.assuming` does not list, with the assumption that says it, if one does; `PremiseNotNeeded(id, premise)`, an outside fact listed that the check does not rest on; `WriterNotListed`, a program writing a store that its `writtenOnlyBy` leaves out; `DeclaredTwice`; `CodeOnlyInStatement`; `Undefined`, a Definition nothing gives a meaning; `DeclarationInCode`, a Declaration reached from proven code; `CodeWithoutClaim`; `PartNotCalled`, a part of a node with proven code that is not a claim about what the code calls) | `ValidatedNec` |
| both, at the shell | `Problems.NotElaborated / Invalid` | raised in `F` (`NoStackTrace`): no operation can continue |
| evaluation | `EvalError` (`Quantified`, `Unbound`, `NoDefine`, `NoCase`, `NoModel`, `Steps`), a plain enum | `Either` in `Evaluate`'s `Run` |
| a program's run in Scala (examples, tests) | `FlowError` (`NotEvaluated(EvalError)`, `NoModel`, `NoOperation`) | raised in `F` (`NoStackTrace`) |
| decisions | `Refusal` (`NotADecider(name)` when the key at hand is not listed under that name) | `Either`: the caller says it and goes on |
| a check | `Finding` cases in `Judged` and `NodeCheck` (`ProofNotAllowed(List[(line, NotAllowed)])`, …); `Result.messages` are Lean's diagnostics; `NotAllowed.LemmaImport` for the shared lemmas | data |
| the theory as a whole | a group with no witness, or one Lean does not check: `GroupStatus.NotProven`, "consistency not proven"; a condition no candidate meets: stated only, "not shown"; an example the code does not meet: `OnCode.Fails`; one setting provided values: "checked in Scala only"; a claim nothing checks (no parts, its tested code unable to judge it): "not checked" | data: a status, not an error (`Warning.ConsistencyNotProven`, `Warning.NotChecked`) |
| tests | `TestReport` with `Against`, `Failure(inputs: List[Value], broke: Broken, …)`, `Made(ty, says)`; `Broken` is `eval.run`'s (`Broken.Always`: an `always[T]` a value of the call breaks; `Broken.Assumption`: an assumption about the values it ran with, broken); `Difference.Answer` or `Difference.State` of a model test | data |
| plain code or a running program evaluating a term with no Scala value | `NotEvaluated(EvalError)`, thrown by `Applied.called`, `Running.value`, `d.fn`, and a function value the evaluator made (`lam`) applied where it has none | production code has no `Either` to return (the documented edge). Inside the evaluator, a `lam`'s host function carries the error out by the same exception and `app` turns it back into `Left` (R9.8: exceptions carry `Either` across host-typed functions; tested that it never escapes as anything else) |
| shell faults (no Lean, unknown node) | `FrFlowError` (`NoStackTrace`) | raised in `F` |
| FrFlow bugs | `IllegalStateException` with "FrFlow bug" | only where the types rule the case out |

Text for the developer is made only in `cli` and `web` (R4). Two kinds of text are data and stay: what the developer
wrote (a reason, a `describedAs`, an exception's message from their code, `Broken.Threw`) and
generated Lean (each obligation's doc comment, made with the obligation by `Required`, `Tries` and `Idle`, as today).

### 4.7 Effects: where `F[_]` is used, and why

The core (`core`, `proof`, `decision`, `Evaluate`, the `testing` generators) has no effect type; `dsl` has
`Flow[F[_]]`, the capability a program is written over, but runs nothing. Where an `F[_]` appears, the table names
what pays for it:

| Algebra or program | Why over `F[_]` | Second interpreter / law / restriction |
|---|---|---|
| `ProjectFiles[F]` | the checker's programs are tested without a disk | in-memory; law: a read after a write gives what was written |
| `Lake[F]` (`Resource`) | the check's planning, caching and judges are tested without Lean | scripted interpreter answering by module |
| `Git[F]` | decision and review tests without a repository | in-memory |
| `LedgerStore[F]` (`Resource` holding the lock) | the CLI and the web view may decide at once | in-memory; law: `update` stores only on `Right`, concurrent updates are serialized |
| `KeyRing[F]` | tests never touch the developer's key | key made in memory; the deciders' list read from `Git`'s committed versions; signing and verifying pure once read |
| `ReadInputs`, `Evaluate`, `CheckProgram`, `NodeChecker`, `DecideProgram` | programs | ask only `Monad`, `Parallel`, `Clock`; cannot do what their algebras do not |
| `FrFlowApi[F]` | the CLI, web and agent suites | in-memory interpreter; law: what `preview` shows is what `decide` records |
| `Flow[F]` (`dsl.flow`) | a program is written once and has two interpreters: Lean's and production's | `Recording` (`Flow[Recorded]`, pure, read into `Prog`) and `eval.Running` (`Flow[F]` for `F: Async`); law: the recording of a program and its run in `IO` agree on the models (the interleavings and model tests check it) |
| a boundary `B[F[_], T[_]]` | the developer's trait; values `Term` in programs and models, plain in adapters | instances derived by `BoundaryOps`: recording, called by name (tests), lifted (production) |
| `FlowInterpreter[F]` | a recorded `Prog` run in Scala on a `World` | `sequential[F: Sync]` (examples, on the models), `concurrent[F: Async]` (interleavings, on the adapters) |
| `Examples[F]`, `Interleavings[F]`, `ModelTests[F]` | classes over a `FlowInterpreter[F]` or `World[F]`, not algebras: each has one implementation | `Sync`; `Interleavings` `Async` + `Random`, deterministic under `TestControl` |

Concrete `IO`: the web server's wiring (http4s routes and `serve`), the CLI's `main` (the composition root that fixes
`F = IO`), and the terminal. In the developer's production code, `IO` is the developer's choice: FrFlow gives
`Running.make[F]` for any `F: Async`, and `knowledge.code(d)(…)` stays a plain function.

### 4.8 The owner's decisions, and what each does to the design

Revision 6 put seven choices to the owner. His answers (`r43-owner-changes.md` §2) supersede the recommendations;
each is applied in the planned code and the plan.

**A. Terms: concrete for the user; final inside (revision 8).** "If it needs to leak to the user then that's bad."
The DSL is written as today (`Term[A]`, `define`, `forall`, `Node.claim(...)`). The owner's later decision
(`r43-owner-changes.md` §5) replaces the "initial inside" half: a `Term[A]` holds a final term, interpreted by each
back end, and its IR is one interpreter's result, kept for the analyses (4.13). Nothing in a model names an
interpreter of terms.

**B. No ambient state.** Both scopes go.
- *Fresh variables* are not made at all (revision 8). A binder's body is a host function (LNCS 7470 §3.2), and each
  interpreter names the variable where it binds it: `ToExpr` by its level (`VarId.level`), `LeanTerm` by the
  developer's name or, when that is taken in scope, the name and the first free number (`x_1`), the evaluator not at all (it
  passes the value). Revision 7's compile-time numbering (`VarId.written`, `AsWritten`'s file and offset,
  `Elab.rebinds`, `Fault.LambdaInItself`) is deleted, and with it round 7's R7.2, R7.5 and R7.6: a helper nested in
  itself is two binders (`NestedHelperSuite`). A recorded program's steps are numbered by the reading of the
  recording, in its own `State` (`VarId.step`, negative, apart from every level).
- *Values in force* are passed to plain code: `implementTested(admit)(env => SessionStore(env(grants), env(sessions)).decide)`,
  `d.fn(env)`. `Param.value`, `Fault.ValueReadWhileBuilding`, `Values.within` and `Fresh` are deleted, and with them
  the `ThreadLocal`s; the examples' 34 uses of `p.value` become `env(d)` when each is ported.
- What remains is one memo in an immutable value (`KnowledgeBase.elaborated`) and production's lock.
  `Captures` (today's reflection on a flow lambda's captured values, to share them as Lean `let`s) is not needed: a
  program shares a value by binding it (`flatMap`), and Lean's `let` is made from that.

**C. Boundaries: tagless.** A boundary is the developer's trait `trait Database[F[_], T[_]]` (`def load: F[T[CrmStore]]`).
The owner's shape is kept with one choice made: in a program and in a model, `T` is `Term`, so a program is
`final class Expiry[F[_]: Flow](db: Database[F, Term])` and every value it computes with is a term written as
everywhere else (a program generic in `T` too would make every term operation in it go through an interpreter, which
A rules out). `F` is abstract, and FrFlow gives it its two interpreters:
- *Lean's*: `Recording`, a pure `Flow[Recorded]`; the boundary's recording instance (`Boundary[Database].recording`,
  derived) records each call; `program { … }` reads the recording into `Prog`, which Lean prints as today's `do`
  block over `[Monad m] [Database m]`, and runs on the models.
- *Production's*: `eval.Running` for any `F: Async`, and the adapter the developer writes over plain values,
  `Database[IO, Id]`, lifted into the program's `Database[IO, Term]` (`database.lifted(adapter, running)`, derived).
- *A model* is an instance of the same trait over a state: `def database[F[_]: Flow](s: Model[F, CrmStore]):
  Database[F, Term]`, recorded into `vocab.StateModel` (`BoundaryOps.model`).

The examples' boundaries (crm's `Database`, sharing's `LibraryStore`, `Mailer` and the clock) and their programs are
rewritten when each is ported. `Flow.effect` (today's production step) is gone: an adapter is plain Scala in `IO`.

**D. A ground-up rebuild in this repository.** The new modules are built from the planned core beside today's, the
examples are ported onto them one at a time, and today's modules are deleted at the end (section 6). Today's Lean is
a reference: an example's Lean may change where the new design is better, and each change is listed and judged.

**E. Twelve modules**: the thirteen designed, less `runtime` (4.3).

**F. Code fingerprint: the simple lexer.** `ScalaTokens` over `Lexer`: comments stripped, blank lines and trailing
spaces dropped, lines and indentation kept, runs of spaces between tokens as one. One `CodeFingerprint`; no `Text`
form, no `tokens:` prefix.

**G. Ledgers start fresh** ("I didn't accept anything": the examples' decisions were made by agents with a demo key).
No `confirm --rebind`, no content forms `V1`/`V2`, no legacy fingerprint, no `Retired` ids, and no old ledger is
read. Each example's ledger is decided anew by the owner once it is ported.

**No run-time checking.** "Once we are in runtime we don't care that much. FrFlow is for testing before production
and strict static guarantees." The `runtime` module goes, with everything that existed only for it; 4.12 says what
that removes, what it simplifies, and where each check it made now happens.

**Flow combinators: all kept.** `race`, `guarantee`/`bracket`, `timeout`, `parTupled`, `ifM` are methods of `Flow[F]`,
each recorded as the step Lean reads (`RecordingSuite`, one test each) and run by `Running` in production; each gets a
use in an example (crm's expiry job, sharing's notifications and housekeeping, section 6).

**Signing: a committed, developer-signed list of who may decide.** `.frflow/deciders` lists each decider's name and
key, and is signed: the first version by its first entry, each later one by a key the version before it listed.
FrFlow reads the file's committed versions (`Git`) and takes the last only when every version follows the one before
(`Deciders.committed`). A decision counts only when its key is listed under its decider's name
(`Deciders.counts`); `DecideProgram` refuses a command whose key is not (`Refusal.NotADecider`) before any rule runs.
Filing a key under a new name, or editing the file without committing a version signed by a listed key, makes no one
a decider.

**Nodes have no `why`.** "Drop why." `Node(id, says, statement)`; the reason is the one given in the node's signed
decision, which `show` and the review read from the ledger (`Says.reason`). An agent's proposal carries its rationale
in the request or the conversation, not in the node. Each example's `why` texts are offered to the owner as the
reasons of its first decisions when it is ported, so nothing written is lost.

### 4.9 Decisions: content, deciders, signatures, fingerprints, review, rules

**Content.** `Content(fields: List[(String, FieldValue)])` with three field shapes (text, texts, record), a canonical
print, `hash` (runs of whitespace ignored) and `ref` (the exact form, which a signature covers). One form, made by
`project.pipeline.Contents.of`: `kind`, `parents`, `parts`, `statement`, `sources`, `substitutions`, `examples`,
`vocabulary`, `uses`, `governs`, `op`, `replaces`, `keeps`, `expects`, `reliance`, `failure`, `implementation`,
`model`, `implementations`. There is no `why` (the reason is the decision's), no `definition` source excerpt, no
`idea` field and no `runtime` field. The fields that render values are one function each in `Texts`, written once for
the new ledgers (today's renderings are a reference); `vocabulary` is `name: means` of every opaque type and symbol
the node speaks of, sorted (`VocabularySuite`). `Meaning.own` (cause `self`) is the content without `parts` and
`parents`; a design keeps its `parents`, since placing a design is what is decided and its chain is empty (DAG §5).

**Deciders.** `.frflow/deciders` is the committed list of who may decide: `Deciders(entries: List[Decider(name, key,
publicKey)], after, seal)`, where `after` is the `ref` of the version before it (none for the first).
- The first version is signed by its first entry, each later version by a key the version before it listed, and names
  that version in its signed bytes (`Deciders.follows`), so an old version committed again names the wrong
  predecessor and breaks the chain: a removed decider cannot be restored by replaying the list that had him (R7.3).
- FrFlow reads the file's committed versions through `Git` and takes the last only when every version follows the
  one before (`Deciders.committed`); a working-tree edit is warned of (`Warning.DecidersUncommitted`) and ignored.
- A decision counts only when its seal's key is listed under its decider's name and the signature verifies
  (`Deciders.counts`); one that does not is shown as not counting (`Warning.NotADecider`) and binds nothing.
- `DecideProgram` checks the key at hand against the list before any rule runs (`Refusal.NotADecider`), so an agent
  with a key of its own, or a key filed under a new name, cannot decide.
- `init` writes the first list with the developer's key. Adding someone is a decision of a listed decider: a new
  version signed by their key, committed.

`DecidersSuite` tests the laws: a decision by an unlisted key, or a listed key under another name, does not count;
a version signed by a key the previous version did not list breaks the chain; an earlier list committed again does
not restore a decider the list after it removed.

**Signatures.** `Payload.of(id, d)` joins, with NUL: node id, action, by, at, reason, rejected, chain, code
fingerprint, commit, after, `content.ref`. It is the new ledgers' own (no older signature is verified).
`Seals.signAdded(before, after, sign)` signs the decisions `after` has that `before` did not, once `Ledger.add` has set
their `after`; `Decide.added` lists them for the shell to report, subjects parents first and then gone nodes.

**Fingerprints.** `CodeFingerprints.of(files)` hashes the governed files, sorted, each as `path NUL text` with a
missing file as `<missing>`, by the simple lexer (`ScalaTokens.significant`): comments blanked (a comment becomes a
space, a newline in it stays), blank lines and trailing spaces dropped, each line's indentation kept as written,
runs of spaces outside literals collapsed. Law, in the direction that matters: an edit that changes what the program
means always moves the fingerprint; edits of comments, blank lines and spacing between tokens do not. Some harmless
edits do move it (`f(/*a*/x)` to `f(x)`, tabs to spaces). `CodeNow.matches` compares a decision's fingerprint with
the code's now.

**Review states.** `Standings(subjects, ledger).all` folds the subjects parents first. Causes: `self`, `above` (the
chain moved, unless only words moved above: `Reworded.only`), `parts`, `code`, `revisit`, `merged`, and a parent
rejected. `Cause.movedUnderCode` (it, or what it rests on, moved and its code did not) lets the CLI say a failing case
as the claim's change.

**Rules.** `Decide(reading, command, author)` refuses a reason of fewer than three words (`Reason.enough`), then
applies one rule class per `Command`: `Accepting` (`accept` with `--revisit`, the mechanical batch `confirm`),
`Rejecting`, `Revisiting`, `Removing` (`gone`); `Below` settles what moved only with an accepted node. A rule makes
each decision with `Decision.taken(action, author, reason, reading.bound(subject))`. The checks reach the mechanical
rule as `Subject.proof: ProofStanding(unproven, partsMake)`, made by `project.pipeline.ReadProof` line for line as
today's `Proofs.unproven` and `partsMake`. `Mechanical.why(reading, subject, others)` is today's chain in its order;
`Reading.notMechanical` folds it parents first. Still `???`: `Reading.waitsFor`, `Meaning.decisionMoved`,
`Below.movedOnlyWith`, ports of today's `Reading`, `Meaning` and `Decide`.

### 4.10 Patterns

The code uses few patterns, each the same way everywhere. One file shows each.

| Pattern | What it is | Example |
|---|---|---|
| Phase | a verb-named object applied to one stage type, giving the next; pure; private helpers below, one idea each | `core/analysis/Validate.scala` |
| Value of | a noun-named type made by `X.of(…)` in its companion | `core/analysis/Shown.scala` |
| Stage type | made only by its phase: an opaque type or a `private[analysis]` constructor | `core/analysis/Valid.scala` |
| Case per kind | an `enum` with only the data of each case; what varies by kind is one match | `core/spec/Statement.scala` |
| Gathered from parts | a `Monoid`, combined with `foldMap` or by every operation | `dsl/build/Declarations.scala` |
| Built later, errors kept | `Deferred[A]`, an `Applicative`; parts combined with `mapN`/`traverse`; a fault before its site is known is a `Fault`, placed once | `dsl/kb/Elaborate.scala`, `dsl/shape/Elab.scala` |
| Algebra of terms, and its interpreters | the term language is `trait X[T[_]]` algebras bundled as `Sym[T]`; a term is `Final[A]`; an interpreter is an `object` or class `extends Sym[R]` for its representation `R` (LNCS 7470 §3.2); a new operation is a new algebra (§2.2) | `core/term/Sym.scala`, `core/term/interpret/ToExpr.scala`, `eval/term/Evaluate.scala`, `proof/lean/term/LeanTerm.scala` |
| Interpreter transformer | an interpreter over another's representation, overriding only what it changes; the rest forwarded once (`Forward`'s `fwd`/`bwd`) | `core/term/interpret/Forward.scala`, `PartialEval.scala`, `Hypotheses.scala`, `Opened.scala` |
| Lowering of structure | a fold over `Prog`/`Prop` (the structure around terms) handing each term to `Printed`; state only where names are made (`State[Naming, _]`) or terms are met (`Writer[OpenTerms, _]`) | `proof/lean/lower/LowerProg.scala`, `proof/lean/lower/LowerProp.scala` |
| Algebra | `trait X[F[_]]` with its laws in the doc, interpreters `make`/`inMemory` in the companion | `project/port/LedgerStore.scala` |
| Capability with two interpreters | what a program may do, `trait Flow[F[_]]`; recorded for Lean (`Recording`, a free structure read into the IR), run in production (`eval.Running`) | `dsl/flow/Flow.scala`, `dsl/flow/ReadRecording.scala` |
| Program | a class over algebras asking the least capability, a `for` of steps | `project/program/DecideProgram.scala` |
| Rule per command | one dispatch match, one class per case returning `Either[Refusal, Ledger]` | `decision/rules/Decide.scala` |
| Derived view | a case class of what front ends show, one function per group | `api/node/NodeViews.scala` |
| Errors as cases | an enum with data; text only in `cli` and `web` | `decision/rules/Refusal.scala` |

Names: one name per concept, none shadowing the standard library (`Iteration.Forall`, not `Some`; `ScalaCode`, not
`Runnable`); one `OpSig` (`core.vocab`). Lean atoms the lowering spells itself go through `lower.Atoms`.

### 4.11 The planned code

`r43-design/` (build in `r43-design/build.sbt`, sources under `src/<module>/`, suites under `test/<module>/`). What to
read first:

| File | What it shows |
|---|---|
| `core/frflow/core/term/Sym.scala`, `algebra/*` (`Logic` … `Annotations`, fifteen), `Final.scala`, `Stated.scala`, `Definition.scala`, `Constructor.scala`, `Case.scala`, `When.scala`, `Selector.scala`, `Ext.scala`; `term/interpret/ToExpr.scala`, `Collect.scala`, `Forward.scala`, `PartialEval.scala`, `Hypotheses.scala`, `Opened.scala`, `Guarded.scala`, `Guard.scala`, `AtValue.scala` | the term language as algebras; the IR (for the analyses), notes, folding, splitting, opening and guarding interpreters (4.13) |
| `core/frflow/core/expr/Expr.scala`, `Prog.scala`, `Pairs.scala`, `PrimOp.scala`, `Iteration.scala`, `Exprs.scala`, `Progs.scala`, `Mentions.scala`; `name/VarId.scala`; `spec/Written.scala`, `Form.scala` | the IR, one operator per meaning; binders by level; programs generic in what a step holds; a term kept with its IR |
| `core/frflow/core/spec/Statement.scala` (three cases), `NodeKind.scala`, `Node.scala`, `Range.scala`, `CallForms.scala`, `CallForm.scala`; `graph/Edge.scala`, `Refinement.scala`; `example/Example.scala`, `Given.scala` | three kinds of nodes, no reason; what a statement ranges over and its reading as a call, derived; a premise beside the parts; an example, a closed fact |
| `core/frflow/core/code/Code.scala`, `CodeTable.scala`, `Impl.scala`, `Values.scala`; `checking/Checking.scala`, `Shown.scala` | what gives a Definition its meaning, built from the values it is given; how a claim is checked |
| `core/frflow/core/analysis/Validate.scala`, `Meanings.scala`, `Scope.scala`, `Guards.scala`, `Premises.scala`, `Outsides.scala`, `Constrained.scala`, `Resolve.scala`, `Callees.scala`; `expr/OutsideFact.scala` | stage types; every Definition given a meaning and no Declaration in code; what an `always` applies to and its hypotheses; the facts about the outside each check rests on; the root statements (claims without parents) and what proven code calls |
| `core/frflow/core/consistency/*` (`Consistency`, `Group`, `Witness`, `Picked`, `Equations`, `Defining`, `Vacuity`, `Conditions`); `proof/frflow/proof/whole/*` (`Joint`, `Possible`, `ExampleGoals`); `proof/lean/lower/LowerWitness.scala`, `layout/WholeModule.scala`; `testing/frflow/testing/search/Small.scala`, `Witnesses.scala` | consistency and vacuity (4.14): the groups, the witnesses derived from the formulas or found by the search, their Lean |
| `dsl/frflow/dsl/build/Deferred.scala`, `Fault.scala`, `Site.scala`, `Declarations.scala`, `Source.scala`, `AsWritten.scala`; `term/Term.scala`, `Terms.scala`, `TermSyntax.scala`, `Implication.scala`, `Data.scala`, `DataMacros.scala`, `CaseMacros.scala`, `Cases.scala`, `Notes.scala`; `Conditional.scala`; `vocab/Declaration.scala`, `Definition.scala`, `OnTheSpot.scala`, `DefinitionSyntax.scala`, `Stating.scala`; `flow/RunFrom.scala`, `Ran.scala`; `model/ModelState.scala`, `StoreModel.scala`, `ModelSyntax.scala`, `AdapterCheck.scala`; `shape/DefineShape.scala`, `Elab.scala`, `Defines.scala`; `node/Node.scala`, `Nodes.scala`, `NodeSyntax.scala`, `AlwaysSyntax.scala`, `OutsideSyntax.scala`, `Edges.scala`; `example/*`; `kb/Elaborate.scala`, `Implementing.scala`, `ValuesSyntax.scala` | the surface and elaboration: the closed `Term[A]`, derived records and eliminators, `when(…)(…).otherwise(…)`, defines called by name, names from the val as written, three node forms, two kinds of values (a Declaration only where a statement is written), `always`, the world outside, a program's claim as a run, a model's state read in a world (`stored.in(before)`), premises, examples as tests; no registry, no ambient state, one error shape |
| `dsl/frflow/dsl/flow/Flow.scala`, `Recorded.scala`, `Recording.scala`, `ReadRecording.scala`, `Boundary.scala`, `BoundaryOps.scala`, `Clock.scala`, `FlowSyntax.scala`; `model/Model.scala` | programs over tagless boundaries, recorded for Lean |
| `eval/frflow/eval/term/Evaluate.scala`, `Run.scala`, `DefSyntax.scala`; `Semantics.scala`, `Env.scala`, `Fn.scala`, `CodeSyntax.scala`, `Running.scala`; `run/CallCheck.scala`, `Made.scala`, `Assumes.scala`, `Wiring.scala`, `ExampleRun.scala`, `OnCode.scala`; `flow/FlowInterpreter.scala`, `World.scala` | the Scala meaning, by the one evaluator of terms; examples on the code; the call check and the wiring tests use; production's interpreter of programs |
| `testing/frflow/testing/PropertyTests.scala`, `ModelTests.scala`, `Runs.scala`, `Respecting.scala`, `Difference.scala`, `Interleavings.scala`, `Case.scala`; `search/StepRefutation.scala` | property-based testing, which carries every check the running service made; an adapter checked against its model; generated values meeting each `always[T]` |
| `proof/frflow/proof/obligation/Prop.scala`, `Obligation.scala`, `Required.scala`, `Tries.scala`, `Idle.scala`, `Discharge.scala`, `Supplied.scala`; `terms/TermTable.scala`, `Terms.scala`, `Keeping.scala`, `Making.scala`; `layout/RefutesModule.scala` | obligations as data, each with its sentence, and what their declarations are applied to; an `always` kept by a run, met by a maker's results; a witness supplied |
| `proof/frflow/proof/lean/ast/*`, `term/LeanTerm.scala`, `term/Scope.scala`, `term/Printed.scala`, `lower/LowerProg.scala`, `lower/LowerProp.scala`, `lower/LowerObligation.scala`, `lower/LowerKeeps.scala`, `lower/LowerWitness.scala`, `lower/LowerValue.scala`, `print/Print.scala` | the Lean back end: every term printed from its final form by the one printer; programs' blocks, propositions and declarations lowered around them |
| `proof/frflow/proof/reading/ProofRules.scala`, `NotAllowed.scala`, `LeanSource.scala` | today's proof-file rules, one case each |
| `decision/frflow/decision/ledger/Deciders.scala`, `Payload.scala`, `Seals.scala`; `content/Content.scala`, `CodeFingerprint.scala` | who may decide, signatures, one content form, one fingerprint |
| `decision/frflow/decision/review/Standings.scala`, `Meaning.scala`, `Reworded.scala`, `Mechanical.scala`; `rules/Decide.scala`, `Accepting.scala` | review as a fold, one rule per command, the mechanical rule |
| `project/frflow/project/pipeline/Contents.scala`, `ReadSubjects.scala`, `ReadProof.scala`, `Analysis.scala`, `Texts.scala`, `Computed.scala`; `code/ScalaTokens.scala`, `Governance.scala`; `program/DecideProgram.scala`, `RunScala.scala` | the content, the subjects, fingerprints, deciding; how a claim is checked, in words; the examples run on the code and the witnesses searched |
| `project/frflow/project/port/*.scala`, `program/*.scala` | algebras, programs with least capability |
| `proof/frflow/proof/lean/lower/LowerModels.scala`; `eval/frflow/eval/flow/World.scala` (`World.models`); `dsl/frflow/dsl/flow/Boundary.scala`, `BoundaryOps.scala`; `dsl/frflow/dsl/model/*`; `testing/frflow/testing/ModelTests.scala`; `test/project/frflow/rooms/Book.scala`, `Rooms.scala`, `BookingsOps.scala`, `StoreModelSuite.scala`, `AlwaysSuite.scala`, `CalendarSuite.scala`; `test/proof/frflow/proof/lean/CrmModels.scala`, `ImplSuite.scala`; `r43-spike/rooms-lean-r15/` | a boundary's model, written, elaborated, printed and run; the assumptions about the outside; an adapter tested against the model; what always holds of the store kept; rooms' Lean compiled and its obligations proven |
| `api/frflow/api/*.scala`, `view/Views.scala`, `view/WholeView.scala`, `Wholes.scala`, `node/NodeViews.scala`, `node/Says.scala`; `wire/frflow/wire/snapshot/*`, `Rows.scala` | the API, the node views (the reason from the ledger, how a claim is checked), the theory's view, the snapshot's rows and their one mapping |
| `test/proof/frflow/proof/lean/CrmModulesSuite.scala`, `ExpiryIr.scala`, `ImplSuite.scala`; `test/proof/frflow/proof/reading/ProofRulesSuite.scala`; `test/decision/frflow/decision/*`; `test/dsl/frflow/dsl/node/NodeSyntaxSuite.scala`, `flow/RecordingSuite.scala`; `test/project/frflow/project/pipeline/VocabularySuite.scala`; `test/project/frflow/rooms/Rooms.scala`, `Book.scala`, `Calendar.scala`, `Knowledge.scala`, `RoomsExamples.scala`, `BookSuite.scala`, `AlwaysSuite.scala`, `CalendarSuite.scala`, `RoomsSuite.scala`, `FormsSuite.scala`, `StoreModelSuite.scala`, `Changes.scala`, `ChangesSuite.scala`, `NestedHelperSuite.scala`; `test/project/frflow/whole/ConsistencySuite.scala`, `VacuitySuite.scala`, `ExamplesSuite.scala`, `CheckingSuite.scala`, `AuthSuite.scala`; `test/project/frflow/auth/Auth.scala`, `AuthExamples.scala`; `test/project/frflow/crm/Crm.scala`, `CrmClaimsSuite.scala`, `RunsSuite.scala`; `test/project/frflow/sharing/Sharing.scala`, `SharingClaimsSuite.scala`; `test/project/frflow/proof/lean/laws/PrinterLawsSuite.scala`, `LeanReader.scala`; `test/eval/frflow/eval/term/TermLawsSuite.scala`, `Generated.scala`, `Slot.scala`; `test/eval/frflow/vocab/*`; `test/eval/frflow/eval/run/ExampleRunSuite.scala`, `WiringSuite.scala`, `RunningSuite.scala`; `test/testing/frflow/testing/PropertyTestsSuite.scala`, `search/SmallSuite.scala` | the evidence |

**The Lean evidence.** `CrmModulesSuite` builds four modules of `examples/crm/lean/FrFlowGen/Crm/` as ASTs and compares
`Print.module` with the files, copied unchanged into `test/proof/resources/crm/`:

- `Boundaries.lean`: `class Database (m : Type → Type)` with its operations, the `DatabaseModel` namespace of `do`
  defs, `structure World`, `instance : Database (StateM World) where logEvent e := …`, and three `@[frflow_defs]
  theorem Database.load_onWorld … := rfl` with parameters and a line break before `rfl`;
- `Domain/Def_expireOnce.lean`: `def expireOnce {m : Type → Type} [Monad m] [Database m] (expire : …)`, its body
  lowered by `LowerProg` from hand-written `Prog`: the form a recorded tagless program takes;
- `Domain/Def_expireOnce_run.lean`: the run on the models (`FrFlow.runOn`);
- `ExpiryJob/Spec.lean`: the post printed by `Printed` from its term (written in final form, as elaboration gives
  it), the claim, and the obligations `impl` and `unsat` lowered by `LowerObligation` from `Prop` over a `TermTable`,
  their formulas printed by `Printed` too.

Today's Lean is a reference, not a constraint (owner D); the suite shows the AST and the lowering can say all of it,
so a difference in a ported example's Lean is a choice, not a limit. `LExpr` has no raw-text case.

**The program evidence.** `RecordingSuite` records a program over a boundary (`Store[F, T]`, its recording instance
written by hand as `BoundaryOps.derived` will make it) and checks each combinator's step: `ifM` (the condition's
program, then a branch), `parTupled` and `race` (both branches held as one step; the race read as the scheduler's
choice), `guarantee` and `bracket` (the finalizer held with the body), `timeout` (the clock read around the program),
`each`, `raise` and `handle`, a bound term shared as a `let`, and a raced branch ending in a shared `let` (R7.4).
`RunningSuite` runs a program in `IO` over `eval.Running`: a condition evaluated, `parTupled` pairing both results,
two programs at once under `atomically` losing no update (R7.8), an error raised and handled; nothing checked.

**The term evidence.** `RoomsSuite` elaborates rooms as the rebuild writes it (`test/project/frflow/rooms/`, the
owner's concepts, one idea per statement): the node's id and the Definition's name from their vals as written, the
calendar's claim one equation (`((granted held request) = (Rooms.isFree held request))`) and a define printed from
their terms, each define called by name, its body printed once over its inputs; `pairwise` and `allDistinct` printed
as Lean's and run by the evaluator; the calendar's words run as Scala and the root's, over every moment, not
evaluated; the claim on `granted` read as its call, its post over `held` and `request`, one equation with no
hypothesis (what always holds of a booking is its `always`'s); the answer the step refutation reads off it.
`FormsSuite` (owner §15): a contract, an invariant, a definition node and an operation do not exist; a Declaration in
a define or a program does not compile, saying why, and code for one does not; a claim applying a Definition to its
leading variables reads as a call, another applied to the same variables is an ordinary mention, and one mentioning
it elsewhere too is still a claim, checked whole; `a implies a implies a` does not compile, either grouping in
parentheses does; a type without `derives LeanType` is named with what to add; renaming a val renames its node.
`CrmClaimsSuite` and `SharingClaimsSuite` (R9.1, R9.2): `saveWrite` and `canViewByAccess` read as calls, with their
Lean; `expiryJob` a run from the world before, its post printed byte for byte as the hand-built IR's and as
`ExpiryJob/Spec.lean`; `handleAnswers` with `.failsChangingNothing`, and a failure clause written as a claim.
`BookSuite` (R10.1, R12.1, owner §11, §16): booking's two claims and the two claims of `always` are the root
statements, and a root on another Definition and a claim relating two validate beside them; each of booking's is one
equation, the store after by `when(…)(…).otherwise(…)` (Lean's `if`), the answer by the store; each check names the
facts about the outside it rests on, and one no assumption says is refused, naming what to say; a fact about the
outside is a premise, never a part, and a premise is an assumption or an `always`; a stray part of the proven code is
refused; `complete` is asked of the calendar's claim and not of the root; the root's `impl` prints as Lean, and so do
the store's model and `bookIfGranted_run` (golden files Lean has compiled). `AlwaysSuite` (owner §13): each `always`
its own claim, of what can be made or of what the store reaches, each a root statement; in Lean every booking a
statement is about comes with `endsAfterStart` as a hypothesis; every run of booking's code keeps each `always` about
the store (`cover_book`, the `keeps_book` declarations, golden files Lean has compiled); a booking ending before it
starts, at a tested Definition's boundary, breaks `endsAfterStart`. `RunsSuite`: a run evaluated on a world (a success
post, a failed run, a failure post), printed as a `match` on its pair, and in the IR a binder of its outcome and the
world after. `ChangesSuite` (R8.2): the rooms model changed in place, a sum matched by its derived eliminator (a case
without fields named by its value), a record updated (`copy`) and made (`make`), a list's `foldLeft`, a `let`, an
option's and an either's fold, each printed as Lean and run. `NestedHelperSuite` is R7.2's helper. `TermLawsSuite` and
`PrinterLawsSuite` are the law suites, `CountSuite` the vocabulary outside the core (4.13).

**The calendar's evidence** (R14.1). `CalendarSuite`: the README's binary-search calendar meets `grantWhenNoOverlap`
on 500 generated cases drawn meeting what always holds (`PropertyTests.of`, `Respecting`), more than 50 of them with
two bookings of one room; on Oak 0–10 and Oak 1–2 (two of a room overlapping) it grants a request for 3–4 the claim
refuses, and that list breaks `roomBookingsApart`, so no case draws it; the README's step-4 calendar is found by a
generated case. `AlwaysSuite`: `made_inRoom` and its `makes_inRoom` as Lean, of `roomBookingsApart` and of
`endsAfterStart`; overlapping bookings are no `RoomBookings` the store gives.

**The whole-theory evidence** (4.14). `ConsistencySuite`: rooms' one bottom claim with an open value, the calendar's,
is its own group, `granted`'s witness its equation's right side, printed as Lean; the state the store starts in meets
each `always` about it; some booking ends after it starts, the search's first. `AuthSuite`: auth's three Declarations,
each its own group witnessed by the equation of the claim refining it for every grant table provided, as Lean; with
no equation for it, a Declaration leaves its group unwitnessed, "consistency not proven". `VacuitySuite`: each
condition is an obligation over the variables bound above it; the search finds a witness of one that can hold and
Lean is given it; one no value meets is left unwitnessed and said so. `ExamplesSuite`: rooms' examples hold of the
calendar's code, one a wrong calendar breaks fails; in Lean each follows from the claims for every meaning of
`granted` they allow; the theory and its obligations are the same without them. `CheckingSuite` pins `show`'s lines
of how each of rooms' claims is checked.

**The testing evidence.** `PropertyTestsSuite` judges generated cases of a plain function against its post through
`CallCheck` and `Wiring` and finds the first that breaks it: the judgement the running service made on a call, made
before production. `ExampleRunSuite`: an example the code meets holds of the code (`OnCode.Holds`); one it does not,
fails (`OnCode.Fails`).
`StoreModelSuite` (R12.1): `stored.checkedAgainst(start = held => …, observe = memory => memory.bookings)` drives
`ModelTests.run` on 200 generated runs of the store's operations (`Runs`, values drawn through `Respecting`, so every
booking meets `endsAfterStart`): the in-memory store agrees with the model; one that forgets the room filter is found at
`inRoom`, one that forgets to add by the state it is read back holding.

**The Lean evidence for rooms** (R12.2; `r43-spike/rooms-lean/`, revision 13; `r43-spike/rooms-lean-r14/`, revision
14). `Dump.lean` is the rooms module as the printer gives it: the defines, `Boundaries.decls.lean`, the program
`bookIfGranted` lowered from its recording, `bookIfGranted_run`, the claims (the calendar's with their guards;
booking's two over their printed posts; the two of `always`), the two `keeps_book` declarations, the obligations
`impl` (both claims of booking) and `cover_book` (both `always`s), and `Whole`: `consistent_0` and
`inhabited_endsAfterStart` proven by their witnesses (`frflow_witness`), `start_neverOverlap` and
`start_endsAfterStart` by `frflow_auto`. `AuthDump.lean` is auth's whole theory, `consistent_0` to `consistent_2`
proven by their witnesses. `lake build` accepts both against a copy of today's `FrFlow` library (Lean 4.35.0) with
`FrFlow/Witness.lean` added (the two tactics, 14 lines), and `open Classical` for the program's `if` on a `Prop` and its
`Prop`-valued result (`Booking → World → (Prop × World)`); the four rooms goldens are in it verbatim. `Proofs.lean`
proves the two `impl`s and the two `cover_book`s (the run's equation, then each by cases on the answer) and checks the
three examples against the claims (`example_0` to `example_2`, `frflow_example`): fourteen theorems, axioms `propext`,
`choice`, `Quot.sound` only, no `sorry`. Revision 15's `rooms-lean-r15/` adds `RoomBookings`, the two
`made_inRoom`s (from `room_apart`: a room's bookings of a store that never overlaps never overlap, by
`apart_noOverlap`), the starts over `initially`, `inhabited_roomBookingsApart` and auth's group solved in
substitution order: eighteen theorems, no `sorry`. Compiling found one gap in revision 13's planned code, fixed then: `LowerProg`
had no case for `atomically` (a transaction is its body on the models).

**Measured** (`r43tools/budget.py` over `r43-design`): no file over 200 lines or 120 columns, no parameter list over
four, one type per file (private helpers and `Term.NoEquality` aside), every package 3 to 15 files (the facade
`frflow` is one file). Over 20 lines are only four single matches over an enum: `Exprs.children`, `Exprs.typeOf`,
`Progs.map`, `Print.expr`. Casts (`asInstanceOf`) are in thirteen places, each with its reason: `Guards`, `Keeping` and
`Making` (a term built from a `Ty`: an `always` rule's define applied to a variable, the elements of a list, a
record's field, a world's state; an operation or a maker applied to its inputs one at a time, each typed by the `Ty`
it is built from); `Definition.called` (a define's body, built by `define` at the curried type of its own `F`); `Term.bound` (the
variable a binder gives its body, for the interpreter that bound it, guarded: another interpreter's use fails
loudly naming the binder, tested; 4.13); `eval.Fn` (the untyped values boundary: `bool`, `as`, `pairs`, and the
developer's functions called and made); `ReadRecording` (a step's result handed to the program's next function,
typed by the step); `Running.handle` (a raised value, typed by its recorded type); `ValuesSyntax.apply` (a value
given under its own Definition); and, new in revision 14, `Defining` and `Conditions` (a witness's or a condition's
variable is an existential `T[Any]`, typed by the IR `Equations` and `Conditions` read first), `AtValue` (an `always`
rule applied to a value of its binder's type, which `Guards` matched by its `Ty`) and `Written.term` (a formula's term,
made only from a `Final[Boolean]`). No interpreter of terms casts, with one exact exception: `Evaluate` reads a
parameter, a free variable, a model's state and a failed run's error from the untyped values it is given, through
`Fn.as` at that boundary (revision 8 said "none"; R8.7). The `implies` macro reads the developer's tree by
pattern, with no cast. No unchecked type test is left outside `Fn`'s calls of the developer's functions:
`Count` is found by its typed key (`Ext`), and a sum's case by its derived test, not a cast. The shapes' casts of
revision 7 are gone: each shape binds its inputs at their own types.

**Size projection.** Today: 12,008 main lines in 347 files. The planned code is the skeleton; the ports the `???`
stand for are estimated from the code they replace:

| Module | Planned now (files / lines / `???`) | Projected lines | Replaces today |
|---|---|---|---|
| `core` | 145 / 3,072 / 0 | 3,000 | parts of `model` (IR, vocabulary, validation), `protocol` (`Walk`, `NodeKind`); consistency and vacuity (new) |
| `dsl` | 69 / 2,182 / 2 | 2,250 | `model`'s DSL, flows as recordings, derivation, source macros (arities 0 to 6 written out) |
| `proof` | 79 / 2,058 / 13 | 2,350 | `lean`, `model`'s `LeanPrinter`, `Types`, `Names`, `Refutation`'s Lean; the whole theory's obligations (new) |
| `eval` | 26 / 719 / 5 | 720 | `model`'s `Eval`, examples, wiring, the production interpreter |
| `testing` | 22 / 428 / 2 | 950 | `model`'s `Testing`, `Refutation`'s search; the witness search (new) |
| `decision` | 42 / 694 / 3 | 750 | `ledger` (less forms, rebind, retired ids), `protocol.decision`, `TrustedKeys` |
| `wire` | 14 / 184 / 0 | 500 | `protocol`'s codecs |
| `project` | 25 / 622 / 12 | 1,050 | `check` |
| `api` | 27 / 381 / 3 | 500 | `api` |
| `cli`, `web`, `agent` | — | 1,650 | the same, less `IdeaSources`, the question numbers and the run-time texts |
| total | 449 / 10,340 / 40 | about 13,700 | 12,008 (and `runtime`'s 400 in revision 6) |

The result is about an eighth larger than today (12% more lines, the consistency and vacuity checks today lacks
among them), in about 570 files instead of 347: smaller files, no type with more than
six fields, and every concept in one place. Revision 8's terms add about 350 lines (the algebras, the
interpreters and their transformer base) and remove the compile-time numbering, the shapes' casts and the
compiled-define memo. Revision 9 adds about 550 (the hard constructs as algebras in every interpreter, the derived
eliminators and `make`, the contract macro, names from the val) and removes about 500 (the IR's printer and evaluator
of terms: `Lower`, `LowerIterate`, `LowerPrim`, `LowerMaps`, `LowerPattern`, `Denote`, `DenotePrim`, `Compiled`;
`Dup`; the arity families `Final1…6`). Revision 10 adds about 460: runs in every interpreter and their syntax,
`Operation`/`Open`, the `implies` check, the list relations, arities three and four, the named contract and the
failure clause. Revision 11 adds about 160 (`Callees`, `impl`, `Validate.code` and `definitions`, `implementProven`,
`Elaborate.vocabulary`, `Ran`, `Node.assumption`), five `???` fewer. Revision 12 adds about 150: `LowerModels`
(which replaces the hand-built `Boundaries` declarations of the crm test), `World.models`, the models in the
vocabulary, and `Modify` in Scala. Revision 13 adds about 280 (the invariants: `Subject`, `Guarded` and `Guards`,
`Keeping` and `LowerKeeps`, `Made`, `Respecting`; the store's model as `StoreModel` with `checkedAgainst` and
`ModelTests.run`, `Runs`; `Edge.Assumes`; `when`) and removes the contract macro (79 lines). Revision 14 adds about
1,000 and removes about 300 (4.14): the consistency and vacuity package and its Lean (389), the world outside (150),
examples as tests (120), how a claim is checked and the theory's view (90), the Definitions' meanings and validation;
less `Promise`, `Expectation`, `Subject`, `Operation`, `Open`, `Arity`, the node examples and their runners, the
evaluations and probes, the answers' invariants and their keeping. Revision 15 adds about 360 (4.14): `made_<maker>`
and its Lean, whole-formula tests and "not checked", record guards, the solving order, one Definition.

### 4.12 What dropping run-time checking removes, and where each check went

**Removed outright.**
- The `runtime` module: `Running` (wiring a service), `Service` and `Guard` (a call checked), `CallValues` (one call's
  values), `AssumptionWatch` (facts re-checked on change), `Sampling` and `Policy` (which calls are checked),
  `Violation`, `ContractViolation`, `Reporter`, `WiringError`, `RunSyntax`; revision 6's `ServiceSuite`.
- In the DSL and core: `.checkedBy(check)` (`Promise.check`, a cheaper check meant for run time), `.checkedAtRunTime`
  (`RunCheck`, `Attachment.runCheck`), `kb.reporting`, `Broken.Check`.
- In Lean: the `check` obligation (post implies `checkedBy`), one per node that had one (crm 4, keycloak 1).
- In content, views and export: the `runtime` content field, `CodeView.runCheck`, `Overview.runChecks`, the snapshot's
  `runCheck`, `Texts.runCheck`; the run-time paragraph of the README's walk-through (step 3) and of USAGE ("Proven,
  tested, assumed"; "checked at run time" in the statements table).

**Simplified.**
- Plain code's values no longer need a scope set around each call: they are an argument (`Values`), which is what
  owner B asks anyway; the `ThreadLocal` and the per-call cells go.
- No shared mutable state is left in production but a program's one lock.
- `knowledge.code(d)(bindings*)` is the wiring `service` did (the bindings over the defines and the other
  Definitions' meanings), returning the plain function; servers call it and lose their `ContractViolation` branches (auth,
  crm, keycloak).
- `Denote.impl` (a proven define run as a service's code) is not needed; `d.fn(env)` covers plain code's use.
- `FlowInterpreter` no longer runs production: programs run directly in the developer's `F` (`eval.Running`), and the
  interpreter runs a recorded `Prog` for examples and tests only (`FlowRun` deleted).
- Two interpreters run a program's branches at once: `FlowInterpreter.concurrent` (the interleavings, over the
  recorded `Prog`, the object Lean proves) and `eval.Running` (production). The interleavings stay on the recorded
  `Prog`, since what they check is the program Lean proved; production's concurrency is tested on its own
  (`RunningSuite`: two programs under `atomically` at once lose no update; R7.8).

**Where each check now happens, and whether anything the owner still needs depended on it.**

| What the running service checked | Now | Depended on? |
|---|---|---|
| a tested contract's result, on every call (or sampled) | `PropertyTests` on generated cases against every claim mentioning the tested Definition, shrinking and saved counterexamples; the examples (`ExampleRun`) | no: the same judgement (`CallCheck`) before production |
| an outside system's adapter, on every call (crm's `recordsByQuery` over SQL, keycloak's `sessionLookup`): crm's seeded SQL bug (the search's `WHERE` dropped) was stopped at the first call that hit it | `PropertyTests` on the adapter's code against its assumption's formula or the define beside it (crm's suite already shows the SQL bug found this way, against `storedMatching`), with generated queries over a test database the example's tests start; its examples; and `ModelTests` against the store's model (`checkedAgainst`) | yes, and it moves: the seeded SQL bug is caught by `check` before production, as a failing case with its inputs; a bug only real data shows is no longer caught when it happens |
| the invariants a contract keeps, on every call | `PropertyTests` (each claim mentioning the Definition; each `always[T]` of the call's values, `Made`) and the examples | no |
| facts about the values a service runs with, when wired and when a value changed (sharing's `HousekeepingOnTime`, "the server checks it as it runs") | under the examples' `:=` values and the tests' drawn values only; otherwise trusted, as every assumption | yes, in one example's wording: the assumption's text loses "checked as it runs"; a deployment that breaks it is not caught |
| keycloak's store promise ("what is stored is read back on every call, so a write the store dropped or changed is seen at once") | `PropertyTests` and examples on the store's code (`StoreKeepsState`'s formula) | the same as the adapter case: caught before production, not when a store misbehaves |
| `checkedBy`'s cheaper check (a property the post implies) | gone with the obligation that proved it from the post | no: the post itself is what tests check |

What remains to trust in production is what is trusted already: the assumptions the developer accepted, FrFlow's
translation to Lean, and, for tested code, the inputs the tests reach. Production code depends on `eval` only to run
its programs and build its code; it never calls back into a check.

### 4.13 Terms in tagless-final style (revisions 8 to 10)

The owner: "Rework architecture to use tagless final approach, especially as specified in
https://okmij.org/ftp/tagless-final/course/" (`r43-owner-changes.md` §5; brief `tagless-brief.md`). The course site
was not reachable from here; the design follows its lecture notes, Kiselyov, "Typed Tagless Final Interpreters",
LNCS 7470 (2012), cited as §n, and Carette, Kiselyov and Shan, "Finally tagless, partially evaluated", JFP 2009
(CKS). Where a choice follows the course's pages beyond the notes (the transformer framework), it says so. Revision
9 makes the final form the only one the back ends read (R8.1), gives the hard constructs their algebras (R8.2), and
replaces the arity families by `lam` and `app` (R8.4). Revision 10 lets a contract name its operation when its
formula applies two (R9.1), gives a program's runs an algebra so a flow contract is written as a claim too (R9.2),
refuses an unparenthesised chain of `implies` (R9.3), carries the owner's list relations (R9.6), and derives a
domain type's `LeanType` once, where it is declared (the spike, R9.7).

**The language is its algebras** (§2.1, the final embedding; §3.2, `Symantics`). `core.term.algebra` has fifteen
small algebras over the representation `T[_]`, split by meaning as §2.2 extends a language:

| Algebra | Operations |
|---|---|
| `Logic`, `Equality`, `Arith`, `Constants` | `bool and or not implies cond`; `eq`; `add sub lt le`; `lit` |
| `Lists` | `nil cons append length`; `all any filter` (one binder); `foldLeft`, `pairwise` (two binders); `nodup` |
| `Options`, `Eithers` | `some none foldOption`; `left right foldEither` (an eliminator with a binder per side) |
| `Quantifiers` | `forall exists` |
| `Records` | `construct` (a constructor as a curried function), `field` and `copy` by a typed `Selector`, `pair` |
| `Sums` | `cases`: a sum's eliminator, one `When` per case (4.13, matching) |
| `Functions` | `lam app let` (§3.2) |
| `Named` | `param` (an open term or an operation), `define` (a named definition) |
| `Variables`, `Annotations` | `free` (a variable bound outside the term); `noted` |
| `Worlds` | `part` (a model's state in a world); `runs`, `fails` (a run of a program from a world: its result, or its error, and the world after, bound by a host function) |

Runs live in `Worlds`, beside the worlds they go between (the package stays at fifteen files). `Sym[T]` bundles
them, with `extension(key)` for algebras added outside the core. Object types are host types
(`T[Boolean]`, `T[List[Booking]]`), so no interpreter tags a value. A term is `Final[A] = [T[_]] => Sym[T] => T[A]`,
a Scala 3 polymorphic function: §2.1's `forall repr. Symantics repr => repr a`, the same value for every interpreter.

**Interpreters** (§3.2; one pattern for terms and programs, 4.10). One printer and one evaluator of terms:

| Interpreter | Representation | Course | Used for |
|---|---|---|---|
| `proof.lean.term.LeanTerm` (`Printed`) | `Scope => LExpr` | §3.2's `S` (`Int -> String`, the depth in, the text out); the scope is passed down, §2.4's context-passing | every term's Lean: claims, defines (once, as their `def`), the terms in programs' steps (`LowerProg`) and in obligations (`Prop.Formula`, `LowerProp`) |
| `eval.term.Evaluate` (`Semantics`) | `Env => Either[EvalError, A]` | §3.2's `R` (there the identity), here a reader of the values given; a quantifier over a whole type has no value | `d.fn(env)`, production's `Running`, examples, generated tests, the steps of recorded programs on the models (`FlowInterpreter`); a run is its program's value (`Program[R]`: from a world, an outcome and a world) applied to the world before |
| `core.term.interpret.ToExpr` | `Int => Expr` (depth in) | §2.4 and §3.3, `initialize`: the initial form; binders by depth | the IR, read only by the analyses of the table below (`Written.value`) |
| `Collect` | `List[Annotation]` | §3.2: another interpreter of the same term | what a term declares and the faults met building it, gathered once at elaboration (R8.5) |
| `Hypotheses[T]` over any `T` | `Split[T, A]` | §2.4: a non-compositional operation as an interpreter of a richer representation | `h1 implies (h2 implies c)` as Lean's `intro h_1 h_2` (written with its parentheses: R9.3) |
| `PartialEval[T]` over any `T` | `Known[T, A]` | CKS §4, the partial evaluator; an interpreter transformer | simplification before printing; later, parameters' values an example fixes |
| `Opened[T]` over any `T` | `Opening => T[A]` | §2.4, context-passing (the context: how many leading `forall`s are still to open, and whether the run below them is) | a claim read as a call, as its post over the call's inputs (R8.3); a program's claim, over its inputs, result, world before and world after (R9.2) |
| `Forward[T, U]` | the base of a transformer | the course's transformer framework (`fwd`, `bwd`, the default instance), from its pages | `Hypotheses`, `PartialEval` and `Opened` override only what they change |

`Dup` is deleted (R8.8): the course's duplicating interpreter exists for terms read from text (§2.3), and FrFlow's
never are; a product interpreter for higher-order abstract syntax cannot split a body `(T1 × T2)[A] => …` into its
two halves, so a term is simply run under each interpreter it needs. Programs over boundaries were already tagless
(4.8.C): `Flow[F]` is their algebra; `Recording` and `eval.Running` its interpreters; the recording's `Prog` holds
the steps' terms as terms (`Prog[Stated[?]]`), and its IR (`Prog[Expr]`, by `Progs.map` through `ToExpr`) is kept
for the analyses as every term's is.

**One printer and one evaluator** (R8.1). Revision 8 printed and evaluated terms from their IR in production
(`Lower`, `Denote`) and from the terms only in tests. Revision 9 deletes the IR's printer and evaluator of terms
(`Lower`, `LowerIterate`, `LowerPrim`, `LowerMaps`, `LowerPattern`; `Denote`, `DenotePrim`, `Compiled`): `Prop`'s
formulas and `Prog`'s terms are `Stated` terms, `LowerProg` and `LowerProp` print only the structure of steps and
propositions and hand each term to `Printed`, and `Semantics` (what `Denote` was: a written lambda as a function, a
constant by its type) runs every term by `Evaluate`. Adding a core operation now touches its algebra, the three
interpreters that represent it (`ToExpr`, `Evaluate`, `LeanTerm`), `Collect` and `Forward`, and `TermSyntax`; the
IR gains a case only when an analysis needs to see it (a match's patterns, a fold's binders). crm's four Lean
files are still printed byte for byte: the post of `ExpiryJob` and the steps of `expireOnce` are written in final
form (`ExpiryIr`) and printed through `Printed` and `LowerProg`.

**Binders are host functions** (§3.2, higher-order abstract syntax). `forall(x)(p: T[A] => T[Boolean])`, `all`,
`any`, `filter`, `foldLeft` and `pairwise` (two variables), the folds of options and eithers, `lam`, `let`, a
match's arms, and a run's outcome and world after (`runs`, `fails`). A binder notes its variables' types, both of a
two-variable binder's (R9.8: `foldEither` noted only its value's, `foldLeft` only its element's).
The evaluator applies the function to the value; `ToExpr` applies it to the variable at its depth
(`VarId.level`); `LeanTerm` names the variable by the developer's name or, when that is taken in scope, the name
and the first free number (`x_1`), never a name its receiver mentions. Nothing is numbered before an interpreter
binds it (`VarId.written`, `AsWritten`'s file and offset, `Elab.rebinds` and `Fault.LambdaInItself` are deleted:
R7.2, R7.5, R7.6). R7.2's helper nested in itself prints `(∀ x ∈ rooms, (∀ x_1 ∈ bookings, (¬(x = x_1.room))))`
(`NestedHelperSuite`).

**Matching, folds, `let`, records: the hard constructs** (R8.2). Each is an algebra operation in the three
interpreters, generated by the laws' generator, and shown in `test/project/frflow/rooms/Changes.scala`:

- *A sum's eliminator.* `c.on[Change.Book](b => b :: held).on[Change.Cancel]((room, start) => …)
  .on(Change.Clear)(…)`, as today, a case without fields named by its value (R9.4; `.on[Change.Clear.type]` before). `Sums.cases(s, arms, ty)` takes one `When[T, S, C, R]` per arm: the case
  (`Case[S, C]`: its names, its fields' names and types, and `test: S => Option[C]`, a type test on `C`'s class
  that `CaseMacros` writes at the call site, so no cast), the case's variable, and the body, a host function over
  the case's term `T[C]`. The developer's function of the case's fields is adapted at compile time
  (`CaseMacros.branch`) to read each field by its derived, typed selector. The evaluator runs the arm whose test
  holds (`EvalError.NoCase` if none: Lean refuses a match that misses a case). `LeanTerm` and `ToExpr` bind the
  case's fields as the pattern's variables and give the body, as the case's term, the constructor applied to them,
  so a field read is the field's variable: `(match c with | Change.Book b => (b :: held) | Change.Cancel room
  start => … | Change.Clear => [])`. A sum's `LeanType` (declaration and `DataRep`) is derived from `Mirror.SumOf`
  by `DataMacros`, as a record's is from `Mirror.ProductOf`, once, where the type is declared (`enum Change derives
  LeanType`: a given in its companion that every use finds). Revision 9 derived it by an inline given at every use;
  the spike below shows why that does not scale. Today's `Cases` casts its result type; this one
  summons it. No cast.
- *Records.* `make[Booking](room, t, t + 1)` (and `Claims(r, u, rs)` through `Data`) is `construct` (the constructor
  as a curried Scala function, derived) applied field by field with `app`, each argument checked against its field's
  type at compile time; an enum's case is a term of the enum. `b.updated(_.start, t)` is `copy` with a selector
  derived where it is written, whose setter is Scala's `copy`. Lean: `(Booking.mk room t (t + 1))`,
  `{ b with start := t }`.
- *Folds and sharing.* `xs.foldLeft(z)((acc, x) => …)` (Lean's `List.foldl` over `fun (acc : B) (x : A) => …`),
  `o.fold(ifNone)(x => …)`, `e.fold(l => …, r => …)` (a `match` on `none`/`some x`, `Except.error`/`Except.ok`), and
  `let(v)(x => …)` (Lean's `let x : T := v; …`).
- *The list relations the owner added* (R9.6, today's `ListRelations`): `xs.allDistinct` (`Lists.nodup`, Lean's
  `(List.Nodup xs)`), `xs.pairwise(apart)` or `xs.pairwise((a, b) => …)` (`Lists.pairwise`, two variables, Lean's
  `(List.Pairwise (fun (a : A) (b : A) => …) xs)`, run on every element with each later one), and `xs.forall(d)`
  with a define `d` (a define is a function of terms, so any binder takes it). Rooms uses all three (below).
- *Runs of a program* (R9.2). `Worlds.runs(p, before, result, after)(post)`: a program's value applied to the world
  before, `post` of its result and the world after; `fails` the same of a run that fails, its error. The evaluator
  runs the program's value (`Program[R]`, Scala's `World => (Either[Any, R], World)`, as Lean's `World → R × World`)
  on the world, a success post holding of a failed run and a failure post of a successful one; Lean takes the pair
  apart, `(match (runExpiry now before) with | (result, after) => …)` (`| (Except.error e, after) => … | _ => True`
  for a failure); the IR is `Expr.Runs`, a binder of the outcome and of the world after, so the analyses see what a
  program's claim mentions (`Expr.RunOn`, which nothing made, and `Expr.Proj` are deleted: R9.8). A program's
  claim's post is the run opened (`Opened`), so neither Lean nor the examples read `runs` there; it is printed and run only
  where a formula states a run itself (`RunsSuite`).

**Named definitions and values: `lam` and `app`** (R8.4). A define is one `core.term.Body[F]` (its name, its curried
type, and its body, a `lam` per input: what the Definition `define` makes carries, 4.14; revision 14 called it
`core.term.Definition`), called with `Named.define` and
`Functions.app` one argument at a time, as Lean applies it; a Declaration's or a Definition's symbol is applied the
same way (`param` then `app`), its Scala value curried at the
values' boundary (`Fn.curried`). The twelve `applied1…6`/`call1…6` methods of every interpreter, `Definition1…6`
and `Final1…6` are gone: four methods per interpreter remain (`param`, `define`, `lam`, `app`). The developer still
writes `define { (a, b) => … }` and `covers(b, t)`; the per-arity code left is the user's syntax (`DefineShape`,
`Definition.apply` (to four inputs, as sharing's claims need), `Declaration.apply` (to three),
`DefSyntax.fn`, written out and
"… to six" as before).

**The user's `Term[A]` is closed and concrete.** `dsl.term.Term[A]` holds `run: Final[A]` and nothing else. The
user writes `Term[Booking]`, `define`, `forall`, `Node.claim(...)` and `b.start`: the README's rooms model compiles
in the owner's forms (`test/project/frflow/rooms/Rooms.scala`, below). `b.start` is `Selectable` with `Fields =
NamedTuple.Map[From[A], Term]`, each field a derived selector with its own `LeanType`. `==` on terms does not compile
(`Term.NoEquality`, today's message). The user never sees `T[_]`, in code or in error messages (the spike below).

The price is one cast. A body is the user's function `Term[A] => Term[Boolean]`, but an interpreter applies it to
its own `T[A]`. `Term.bound(owner, x)` wraps that value as a term that is `x` for the interpreter that bound it (`s
eq owner`) and fails at once for any other ("FrFlow bug: a bound variable used outside its binder", tested in
`TermLawsSuite`, R8.7). The alternative, a `Term` that names `T`, would show `T` to the user.

**Notes are an interpretation** (R8.5). What a term declares (types, symbols, defines) and the faults met building it
are on the term itself, where they arise (`Annotations.noted`: a constant notes its type or its fault, a parameter
its symbol, a call its define, a binder its variable's type), and gathered once at elaboration by the `Collect`
interpreter, which runs each body once on a variable that carries nothing. No operation merges notes; the sentinel
variable and the second build of every body are gone. Every interpreter passes `noted` through; a transformer keeps
its own information across it (`PartialEval`, `Hypotheses`, `Opened`).

**Closed `Term`, open vocabularies** (§2.2, the expression problem). `Term` is closed over `Sym`. A vocabulary added
outside the core is one of two things:
1. defines, named definitions in the core language: most of a project's vocabulary (rooms' `covers`, `apart`);
2. a new algebra, for an operation the core cannot say well. `Count[T]` (`test/eval/frflow/vocab/`, outside `core`
   and `dsl`) is the example: its syntax builds a `Sym` term whose run asks the interpreter for its own instance by a
   typed key (`s.extension(Count)`, R8.6): an interpreter that implements `Count` returns itself for the key, matched
   on the key's type (`case _: Count.type => Some(this)`: `E` is `Count`, so no cast and no unchecked test); any
   other returns `None`, and the term runs the operation's meaning in the core (`length(filter(…))`). A transformer
   forwards no extension: `PartialEval` over an interpreter that knows `Count` runs the meaning (tested).

Not taken: a `Term` indexed by the set of algebras it needs (an open union of type classes), since the user would
then write algebras in types.

**What is not compositional: context, or the initial form** (§2.4; §3.3 shows the two forms are isomorphic).

| Need | Form | Why |
|---|---|---|
| the code fingerprint of definitions | neither: the source | it hashes the governed Scala as the simple lexer reads it (owner F, 4.9), not terms |
| the "what changed" view of a decided node | initial (`Written.value`, `Statement`) | it compares two elaborations; final terms have no equality, the IR does |
| the refutation search, and its hint naming the changed define | initial (the IR, `Mentions`) to find the defines a failing step calls; final (`Evaluate`) to run the step | inspecting needs the IR; running does not |
| splitting `implies` into hypotheses | final: `Hypotheses` | compositional once it returns the parts with the whole |
| named definitions printed once | final: `Named.define` prints a name; `Printed.define` prints the body once | a define is a value with its name, never inlined |
| Lean module layout | initial (`Theory`, `Vocabulary`, `Resolved`) | it reads which nodes and defines exist and what each mentions |
| simplification before printing | final: `PartialEval` over `LeanTerm` | a transformer composes with any interpreter (CKS §4) |
| obligations, and substituting a node's open terms | the structure initial (`Prop` over node names), each formula as written (`Prop.Formula(Written[Expr])`: its term printed by `Printed`, its open terms read from its IR, made once: R9.8) | combining statements reads their structure; a formula is printed as every term is |
| a claim read as a call, as its post | final, context-passing: `Opened` | the leading `forall`s become the call's inputs; the Definition stays a symbol, given the call's result when checked |
| a program's claim, as its post | final, context-passing: `Opened` with its run | the inputs and the world before, then the run's result and world after, become the post's four kinds of input, as today's Lean states them |
| each `always[T]` as a hypothesis on every variable it applies to (owner §13) | final: `Guarded`, a transformer of `forall` and `exists` only (each guard built over any interpreter from the variable's `Ty`: `Guards`) | a statement says one thing; what always holds is added where Lean states it, never written into it |
| which Definition a claim reads as a call of, and that it is mentioned only so | initial (the formula's IR: `CallForms`) | a check of where a symbol occurs, not a meaning |
| a consistency witness from an equation; each condition of `implies` with what is bound above it (4.14) | final: the transformers `Defining` and `Conditions`, after the IR says where (`Equations.defining`, the condition's place) | a witness and a condition are terms, printed by the one printer and run by the one evaluator |
| naming binders uniquely in Lean | final, context-passing: `LeanTerm`'s `Scope` | the names in scope are a context passed down |

So the IR is read only by the analyses (what changed, mentions and open terms, the refutation's hint, the layout,
`Validate`'s and `Resolve`'s reading of statements), and it is made by an interpreter: `Written(value, source, form)`
holds the term (`Form.Term(Stated)`) or a program's recorded steps (`Form.Steps(Prog[Stated[?]])`) and their IR
(`value`, made only by `Written.formula`, `Written.lambda` and `Written.steps`, through `ToExpr`).

**The user's forms** (R8.3, R9.1–R9.6, R12.1; the owner's decisions, `r43-owner-changes.md` §6, §10 and §13–§18,
which today's library adopts too). Three kinds of nodes, two kinds of values, `forall` and `always` (4.14). One idea
per statement, a style guide: what always holds is its own claim of `always`. Rooms as the rebuild writes it
(`test/project/frflow/rooms/Rooms.scala`, `Book.scala`, `Calendar.scala`, `Knowledge.scala`, `RoomsExamples.scala`;
revision 15's, 4.14), and a claim of crm (`test/project/frflow/crm/Crm.scala`):

```scala
final case class Booking(room: String, start: BigInt, end: BigInt) derives LeanType

/** A room's bookings, as the store gives them. */
final case class RoomBookings(bookings: List[Booking]) derives LeanType

val granted = Definition[(RoomBookings, Booking) => Boolean]("whether a request is granted, given the room's bookings")
val book = Definition[Booking => Program[Boolean]]("booking a request: whether it was booked")

val covers = define { (b: Term[Booking], t: Term[BigInt]) => b.start <= t && t < b.end }
val apart = define { (a: Term[Booking], b: Term[Booking]) =>
  a.room =!= b.room || forall((t: Term[BigInt]) => !(covers(a, t) && covers(b, t))) }
val isFree = define { (held: Term[List[Booking]], request: Term[Booking]) => held.forall(b => apart(b, request)) }
val noOverlap = define { (a: Term[Booking], b: Term[Booking]) =>
  a.room =!= b.room || a.end <= b.start || b.end <= a.start }

// the world outside
val storeModel = Node.assumption("The store gives a room's bookings oldest first, and adds one last.")(
  store.behavesAs(stored))
val startsEmpty = Node.assumption("The store starts with no bookings.")(stored.initially(held => held === Nil))
val onlyBookingWrites = Node.assumption("Only booking writes the store: no other program or person changes it.")(
  stored.writtenOnlyBy(book))
val oneAtATime = Node.assumption("Bookings are processed one at a time: one server process runs each atomically.")(
  stored.changedOneRunAtATime)
val fromTheForm = Node.assumption("Requests come from the booking form, which refuses one ending before it starts.")(
  outside.calls(book))

// what always holds
val endsAfterStart = Node.claim("Every booking ends after it starts.")(always[Booking](b => b.start < b.end))
  .assuming(fromTheForm, storeModel, oneAtATime, startsEmpty, onlyBookingWrites)
val neverOverlap = Node.claim("The bookings held never overlap.")(always(stored)(held => held.pairwise(apart)))
  .assuming(storeModel, oneAtATime, startsEmpty, onlyBookingWrites)
val roomBookingsApart = Node.claim("A room's bookings, as the store gives them, never overlap.")(
  always[RoomBookings](r => r.bookings.pairwise(noOverlap)))
  .assuming(storeModel, neverOverlap)

// the roots, about `book`
val bookWhenFree = Node.claim("A request is booked exactly when its room is free.")(
  forall((request: Term[Booking], before: Term[World]) =>
    val held = stored.in(before)
    book(request).from(before) { (_, after) =>
      stored.in(after) === when(isFree(held, request))(held :+ request).otherwise(held) }))
  .assuming(storeModel, oneAtATime)

val answersWhetherBooked = Node.claim("Booking answers whether the request was booked.")(
  forall((request: Term[Booking], before: Term[World]) =>
    book(request).from(before) { (booked, after) => booked === (stored.in(after) =!= stored.in(before)) }))
  .assuming(storeModel, oneAtATime)

// the calendar, over what the store can give
val grantWhenFree = Node.claim("A request is granted exactly when its room is free for its whole time.")(
  forall((held: Term[RoomBookings], request: Term[Booking]) =>
    granted(held, request) === isFree(held.bookings, request)))
  .refines(bookWhenFree)

val grantWhenNoOverlap = Node.claim("A request is granted exactly when it overlaps no booked time.")(
  forall((held: Term[RoomBookings], request: Term[Booking]) =>
    granted(held, request) === held.bookings.forall(b => noOverlap(b, request))))
  .refines(grantWhenFree)

// Book.scala
val store = Boundary[Bookings]("the SQLite table the bookings are kept in")

/** The store as the proofs see it: every booking, oldest first; a room's, as the store gives them. */
final class Stored[F[_]: Flow](state: Model[F, List[Booking]]) extends Bookings[F, Term]:
  def inRoom(room: Term[String]) = state.get.map(held => make[RoomBookings](held.filter(b => b.room === room)))
  def add(booking: Term[Booking]) = state.get.flatMap(held => state.set(held :+ booking))

val stored = store.model("every booking the store holds, oldest first")(Stored(_))
val bookIfGranted = program { (request: Term[Booking]) => BookIfGranted(store.recording).run(request) }

// Knowledge.scala
val rooms = KnowledgeBase("Rooms")(bookWhenFree, answersWhetherBooked, neverOverlap, endsAfterStart,
  roomBookingsApart, grantWhenFree, grantWhenNoOverlap, storeModel, startsEmpty, onlyBookingWrites, oneAtATime,
  fromTheForm)
  .implementProven(book)(bookIfGranted)
  .implementTested(granted)(_ => (held, request) => Calendar(held).grants(request))

// RoomsExamples.scala: tests beside the knowledge base, nothing depends on them
class GrantedExamples extends FrFlowExamples(rooms):
  example("back to back: granted"):
    granted(RoomBookings(List(Booking("Oak", 9, 10))), Booking("Oak", 10, 11)) is true

// crm
val saveWrite = Node.claim("A write is stored, and the rows about its record are returned as read back.")(
  forall((s: Term[CrmStore], w: Term[WriteCmd]) => save(s, w) === aboutRecord(write(s, w), about(w))))
```

Each statement says one thing, as one equation (the readers' `before(Stored)`, the Boolean `fold`, `.refines` on an
assumption, the two contract shapes and the two names per node are gone, R12.1; the contract, the invariant, the
model and the definition as kinds of node, `Operation` and `Open`, owner §15):

- *Booking, one idea per statement.* `bookWhenFree` is the purpose, one equation over the store: the bookings held
  after are the ones held before with the request added when its room is free, and the same otherwise. It says
  nothing of overlaps: that the bookings held never overlap is its own claim, `always(stored)`, and the Booking's
  `start < end` is its own, `always[Booking]`. **Book's Boolean answer** is not a second conjunct: it is a second
  claim, `answersWhetherBooked`, one equation that says what the answer means, "booked exactly when the bookings held
  changed". Both are claims about one Definition, `book`, and root statements (owner §11: several are allowed);
  `implementProven(book)(bookIfGranted)` gives `book` its meaning once, and Lean proves the program meets each (one
  `impl` per claim; `r43-spike/rooms-lean-r15/Proofs.lean`).
- *What always holds* (owner §13, §15; revision 13's invariants; revision 15 adds `always[RoomBookings]`, 4.14).
  `always[Booking](b => …)` is about every value of
  the type that can be made: Lean takes it as a hypothesis on every value of the type a statement is about (each
  booking, each element of a list of them, each booking a world's store holds: the `Guarded` transformer, below); it
  is checked where a tested Definition makes a value (`Made`, `Broken.Always`), every generated value meets it
  (`testing.Respecting`), and the values entering from outside meet it by an assumption (`outside.calls(book)`).
  `always(stored)(held => …)` is about every state the store reaches: every claim over a world may assume it of the
  world before (the same transformer), and every program writing the store is asked to keep it, `cover_book : ∀
  granted, ∀ h_grantWhenFree, neverOverlap.keeps_book (bookIfGranted_run granted)`, every run from a world meeting
  every `always`, on inputs meeting theirs, ending in one meeting it (`Keeping`, `LowerKeeps`), from the state the
  store starts in (`start_neverOverlap`); that this covers every state reached rests on the four facts about the
  store (4.14). An `always[T]` of a type a store holds is kept the same way. Neither has parts or parents: each is a
  root statement. The calendar's claims are each then one equation, with no hypothesis written: the claim's Lean, as
  `AlwaysSuite` prints it, is `∀ (held : RoomBookings), (∀ b ∈ held.bookings, endsAfterStart b) → roomBookingsApart
  held → ∀ request, endsAfterStart request → granted held request = isFree held.bookings request`.
- *The conditional*: `when(c)(a).otherwise(b)` (`Conditional`; Lean's `if c then a else b`), each branch named where
  it is written. `Term[Boolean].fold(ifTrue, ifFalse)` is gone; an option's and an either's folds stay, their arms
  typed differently. Scala's own `if` cannot be lifted without a macro over the developer's tree, and `when` reads as
  plainly.
- *A model's state, read in a world*: `stored.in(before)` (was `before(stored)`).
- *Names from the val* (`Source.valName`): a node's id is its val's name as written (`grantWhenNoOverlap`), the one
  name it has in code, in reports and in Lean's namespaces (R12.1); a Declaration's, a Definition's, an `Opaque`
  type's, a `Boundary`'s and a model's name is the val's. An id cannot stay stable under a rename without a second
  name to keep it, so renaming a val renames the node: it is a new node to decide, which `.replaces(old)` links to the
  old one.
- *`Declaration[A]` and `Definition[A]`* (owner §14, §15; they replace revision 10's `Operation[F]` and `Open[A]`
  and today's `Param`): a Declaration is abstract, of any type, applied only where a statement is written (its
  `apply` asks for a `Stating`, which only `Node.claim`, `Node.assumption` and `example` give); a Definition, of any
  type, is a term code and programs use, given its meaning once in the knowledge base (`implementProven`,
  `implementTested`, `implementValue`, `implementProvided`) or where it is written (`define`, `program`). No `Arity` is needed: the
  function's type is the value's type.
- *`implies`*, alphanumeric, so it binds last: `a && b implies c` is `(a && b) implies c`, and `p implies q === r` is
  `p implies (q === r)`, as they read (tested). `==>` is deleted: its precedence (that of `=`) bound it tighter than
  `&&` and `||`. Every alphanumeric operator groups to the left in Scala, so `a implies b implies c` would be `(a
  implies b) implies c`; `implies` is a macro that refuses that chain at compile time unless its left operand is in
  parentheses, saying so (R9.3; `FormsSuite`): the developer writes `a implies (b implies c)` or `(a implies
  b) implies c`.
- *A claim read as a call* (owner §15; it replaces revision 12's one contract shape and its elaboration checks
  `OperationElsewhere`, `NotOverInputs`, `NoRun`): where a claim applies one Definition to exactly its leading
  `forall` variables, alone or as one side of its equation, and mentions it nowhere else, `CallForms` reads it as a
  call of that Definition, so tested Scala for it is checked call by call; another Definition applied to the same
  variables (`write(s, w)` beside `save(s, w)`) is an ordinary mention. Its post is the formula with those `forall`s
  opened (`Opened`): a lambda over the call's inputs in which the Definition stays a symbol; a call is checked by
  giving the symbol the call's result for those inputs (`CallCheck.answer`). A claim that reads as no call is not
  refused: it is checked as a whole, its Definitions given their meanings (`FormsSuite`).
- *A program's claim, a run* (R9.2): `forall((request, before) => book(request).from(before) { (booked, after) =>
  … })`. `CallForms` reads it as a run of the Definition when what is below its inputs and the world before is the
  run of the Definition on exactly them and the Definition is mentioned nowhere else; `Opened` opens the run, so the post is over `(request, booked, before, after)` as today's
  Lean states it (crm's `ExpiryJob` prints byte for byte as `test/proof/resources/crm/ExpiryJob/Spec.lean`,
  `CrmClaimsSuite`). What a failing run gives (R10.3): one run with both outcomes, as a match states its cases,
  `handle(r).from(before) { (answer, after) => … }.failing { (error: Term[Failure], after) => … }` (`Ran`);
  `CallForms` takes the success side as the post and the failing side as the failure clause
  (`SharingClaimsSuite`). `.failsChangingNothing[Failure]` on the run stays for the common case, a failure that
  changes nothing.
- *A service's root statements about its entry flow* (R10.1; the owner's rooms, §9, §11). Booking's statements have
  no parents, so they are root statements, beside the claims of `always`; a knowledge base may have several, on any
  Definitions, including a statement relating them (`BookSuite`: a claim on another Definition and a claim relating
  `book` to `granted`, beside booking's, validate). Its code is a proven program, so each is proven by `impl` from its parts, not by `complete`:
  `grantWhenFree` (about `granted`, which the program calls) is the root's hypothesis; the answer's statement has no
  parts, so its hypotheses are what its code relies on (`grantWhenNoOverlap`, the claim on `granted`). The store's
  model is a premise, `storeModel` (`store.behavesAs(stored)`, written `.assuming(storeModel, oneAtATime)`): it is
  in `bookIfGranted_run` itself, the run on the models, never a part. The root's `impl` obligation, as `BookSuite` prints it:

  ```
  /-- Every result of bookIfGranted_run meets bookWhenFree, given what grantWhenFree promise. -/
  @[frflow_defs] def impl : Prop :=
    ∀ (granted : RoomBookings → Booking → Prop), ∀ (h_grantWhenFree : (Rooms.grantWhenFree.claim granted)),
      (Rooms.bookWhenFree.claim (Rooms.bookIfGranted_run granted))
  ```

  A root about a program has no `idle` try: a run has no "nothing" to give (`Substitute.canDoNothing`).
- *The store's model* (R11.1, R12.1). `val stored = store.model(means)(Stored(_))` declares the model with its
  instance (`ModelSyntax`; a `StoreModel[Bookings, List[Booking]]`: the state, `stored.in(world)`, and `Stored`), so
  one val names both, and `Stored` is only the model's class. `Stored` is written as a program is: an instance of the
  boundary's trait, over the model's state (`Model[F, S]`: `get`, `set`) instead of over boundaries; it is recorded
  once on each operation's parameters' variables (`BoundaryOps.model`, through `ReadRecording`) into the
  vocabulary's `StateModel`, beside the boundary's `BoundarySig`. `Node.assumption(statement)(store.behavesAs(stored))`
  is the decided assumption that the store behaves so (4.14). `LowerModels` prints them as today's `Boundaries.lean` (the class, the
  model's operations as `do` blocks on its state, `World`, the instance on `StateM World`, its lemmas), and a
  program's run, `bookIfGranted_run … := fun request w => (FrFlow.runOn ((Rooms.bookIfGranted granted) request) w)`,
  runs it on that instance. A program's Boolean result is Lean's `Prop` there, as terms' are (`(Prop × World)`;
  Lean's classical `if` decides it); Lean accepts the printed rooms module, and the four obligations are proven
  (R12.2, 4.11). crm's `Boundaries.lean` and `expireOnce_run` print byte for byte from crm's boundary, model and
  program (`CrmModels`, `CrmModulesSuite`).
- *An adapter checked against its model* (R12.1): `stored.checkedAgainst(start = held => Ref[IO].of(held).map(Memory(_)),
  observe = memory => memory.bookings)`, an `AdapterCheck`: how the implementation is made holding a state of the
  model, and how its state is read back. `ModelTests.run(check, semantics, vocabulary)(held, steps)` makes both
  holding `held`, runs the generated calls on each (the adapter by name, `BoundaryOps.call`; the model by
  `World.models`), and reports the first call answered differently (`Difference.Answer`) or, after the last, the
  state read back when it is not the model's (`Difference.State`). The calls are generated from the boundary's
  signature (`Runs`), each argument drawn by its type and meeting each `always[T]` of it (`Respecting`). `StoreModelSuite`
  writes exactly this; the hand wiring (a `World` adapter, `BookingsOps.call`, hand-made `Step`s) is gone.
- *`BoundaryOps`* for a trait `B[F[_], T[_]]`, which `derives BoundaryOps` (a macro, `???` here) will write and which
  rooms' `BookingsOps` writes by hand, all five members: `className` and `ops` (the trait's methods' signatures, the
  class Lean declares); `recording` (each method a `Recorded.Call` of its arguments, typed by its result); `call` (an
  adapter's method by name on plain values, for the model tests); `model` (each method of the developer's model
  instance, recorded on its parameters' variables, its steps read); and `lifted` (R12.3), production's path
  (`knowledge.running`). For `Bookings[IO, Id]`, `lifted(adapter, values)` is a `Bookings[IO, Term]` whose
  `inRoom(room)` evaluates `room` to its `String` (`values.value`, the evaluator under the running program's values:
  `Terms`, which `eval.Running` is), calls `adapter.inRoom` on it, and makes the `List[Booking]` it gives a term again
  (`values.term`, by `LeanType[List[Booking]]`); `add(booking)` evaluates its argument and calls `adapter.add`. Nothing
  is checked: the adapter was tested against the model (`checkedAgainst`). `StoreModelSuite` runs `BookIfGranted` in
  `IO` over `Running` on the in-memory store lifted so: a free request is booked, a clashing one is not, and the store
  holds the first.
- *`.refines(parent)`* instead of `.under(parent)`: the refinement calculus' word for what the edge means.
  `.assuming(premise)` (new) for a premise: an assumption or a claim of `always` the proof assumes, never a part.
- *Examples* (owner §18; they replace R9.4's `allows(…, returning = r, "label")` and `forbids(…)`, `dsl.node.Call`
  and the rule that a contract has a `forbids`): `example(name, d := v)(fact)`, the fact a closed formula (`t is
  true`, `t is v`), in a `FrFlowExamples(kb)` class beside the knowledge base, each value reified by its type where written
  (4.14).

**De-serialization** (§2.3). The course typechecks untyped trees into final terms because its terms come from text.
FrFlow's do not: a term is built only by the developer's Scala, compiled by Scala. The ledger stores contents and
decisions (text and hashes), never a term to rebuild; the API, the web front end and the agent send commands and
ids, and the agent edits Scala. So no typechecker is needed.

**Optimisation is an interpreter** (CKS §4). `PartialEval` folds what is known (`1 < 2 && p` is `p`); a known left
operand decides `&&`, `||` and `implies`, a known right one only drops itself, so an operand with no Scala value (a
quantifier) is still met in the same order and the laws hold. Each fold makes its constant with the maker its
operation gives (`bool`, a number), with no type test (R8.9).

**Laws** (R8.10). On 300 generated terms reaching every algebra but runs (a match over an enum, the folds, `let`, a
record made and updated, defines called and passed as functions, `allDistinct`, `pairwise`; `TermLawsSuite` checks
the IR shows each), each body rebuilt from its own seed so every interpreter sees the same term. Runs are not
generated: a program's value is not a constant a term can hold, and the laws' terms are closed; `RunsSuite` runs,
prints and initializes them on given programs instead.
- the examples' path means what the evaluator means: a written lambda run on arguments (its inputs bound at their
  levels, as examples and generated tests run it) gives the evaluator's value of the same term over the arguments as
  constants;
- constant folding keeps every value; the IR is typed as the term (`Exprs.typeOf` is `Bool` for a formula);
- the printer's text reads back (`PrinterLawsSuite`): print, read (`LeanReader`, a reader of exactly the Lean the
  printer writes, refusing anything else), print gives the same text, for every term, and for every term folded
  first (never longer); split into hypotheses, a term printed whole is the term printed; an obligation's formula
  prints as the term does.
Deciding the printed Lean for generated terms (Lean agrees with the evaluator) is the next law (step 3), once `lake`
runs in the suite; the reading law above is its pure-Scala half. Two more evaluator laws (R9.8): a function value
the evaluator makes, applied outside it where it has no value, throws `NotEvaluated` (the plain-code path's
documented edge, as `d.fn` does), and inside it `app` gives `Left`; a two-variable binder notes both types.

**Spike: compile time and error messages, before and after** (`r43-spike/`; R9.7). Today's FrFlow (a copy of the
repository outside it) and the planned code each compile, alone and from clean, 15 times in one warm sbt:
- rooms: the same definitions in each one's forms (today's `Knowledge.scala`: five defines, an operation, a claim and
  a contract, with `pairwise` and `forall` of a define; its two examples left out of both);
- sharing's largest match file, `SharingHttp.scala` (26 matches over a 13-case enum, `let`, the folds), its three
  defines kept as written and its types and operations cut down to what they read, so it compiles alone in both
  (`spikesharing/Requests.scala`; today's copy made from the planned one by two mechanical rewrites).

The compiler's time per run (`<project> / Compile / compileIncremental`, logs `r43-spike/*-runs5.log`, numbers
`timings5.txt`). Each run list starts with a compile of the already compiled project (7 to 15 ms), then the first
clean run, cold, then fourteen more; round 4's table took its second entry as the first clean run, which is right,
but the reviewer read its first, 13.3 s, which was a full compile of a never-compiled spike (R9.7):

| | first clean run | median of the last 8 | fastest |
|---|---|---|---|
| rooms, today | 6.0 s | 0.60 s | 0.49 s |
| rooms, planned (revision 10) | 6.4 s | 0.80 s | 0.73 s |
| sharing's match file, today | 12.7 s | 2.44 s | 1.95 s |
| sharing's match file, planned (revision 10) | 12.1 s | 2.38 s | 2.10 s |

Rooms costs about 0.2 s (1.3 times) more per clean compile, from the contract macro (gone since revision 13), `implies`' check and the
derived eliminators' setup; sharing's file, where the matches dominate, costs the same as today. The machine was not
quiet: no sbt of this session ran beside the measurement, but three of other sessions did (load average about 3 on
four cores throughout), so these are comparisons run back to back, not absolute numbers.

The measurement found a defect. Revision 9 derived a domain type's `LeanType` by an inline given, expanded at every
use: each operation's type and each arm re-derived `Library`'s and `Request`'s whole structure, and sharing's file did
not compile at all ("Method too large: `Operations$.<clinit>`", "Class too large: `Handling$`"). A type now derives
its `LeanType` once, where it is declared (`enum Request derives LeanType`), and every use finds that given; without
`derives`, a use says "no LeanType for Request". Step 2 keeps this spike in its build.

A type error inside a define (`t < b.room`, a moment compared with a room), a body that is not a condition
(`held.forall(b => b.start)`), and `==` on terms each give the same message before and after, naming no
interpreter:

```
Found:    frflow.dsl.term.Term[String]      (today: frflow.term.Term[String])
Required: frflow.dsl.term.Term[BigInt]      (today: frflow.term.Term[BigInt])

Found:    frflow.dsl.term.Term[BigInt]      (today: frflow.term.Term[BigInt])
Required: frflow.dsl.term.Term[Boolean]     (today: frflow.term.Term[Boolean])

FrFlow: compare terms with === (and =!=), not == …   (as today)
```

The first and the third are followed, in both, by a second error on the define's result type (`Ambiguous given
instances … LeanType[R]`): Scala 3 has no `@implicitAmbiguous`, so that one stays; the first error is the one to
read. A type used in a term without `derives LeanType` now says so (R10.2): "Plain is not a domain type yet: add
derives LeanType to its declaration" (with the code quoted) (`@implicitNotFound` on `LeanType`; `FormsSuite`).

### 4.14 The owner's core concepts: three kinds of nodes, two kinds of values, two quantifiers (revisions 14 and 15)

The owner (`r43-owner-changes.md` §15): "three kinds of nodes + two kinds of values + forall, always … Those
decisions are important, so make sure they are reflected in the design strictly and not worked around." Revision 14
applied §10–§18 to the planned code; revision 15 answers review round 14 (`r43-review-14.md`): one user type for a
Definition (R14.2), premises written with `.assuming` (R14.3), the calendar's claims over what the store can give
with `made_<maker>` written (R14.1), today's library's names (R14.4), claims tested whole (R14.5), consistency groups
solved in substitution order (R14.6), and one `implement…` pattern (R14.7). Nothing of the removed kinds is kept
under another name: `Node.contract`, `Node.invariant`, `Node.definition`, `Operation`, `Def1`, `Def2` and `Steps` do
not compile (`FormsSuite`), and no type, case or method in `src/` is named for them.

| Concept | Where | What it replaces (deleted) |
|---|---|---|
| a node: claim, assumption, design | `core.spec.Statement` (three cases), `NodeKind` (three), `dsl.node.Node.claim/assumption/design` | `Statement.Stated(formula, Trust, Reading)`, `Trust`, `Reading`, `Subject`, `Expectation` and `.expects`, `Promise`, the contract, invariant, model and definition kinds |
| a value: Declaration, Definition | `dsl.vocab.Declaration`, `Definition` (with `OnTheSpot`, the meaning `define` and `program` give it), `Stating`; `core.vocab.ValueKind`; `core.code.Code` (`Proven`, `ProvenFlow`, `Tested`, `Valued`, `Provided`) | `Operation`, `Open`, `OpenTerm`, `Arity`, `Code.ProvenBeside`; revision 14's `Def`, `Def1`, `Def2`, `Steps` (R14.2); the core's `term.Definition` is `term.Body`, a define's named body |
| the quantifiers: `forall`, `always` | `Quantifiers.always`; `spec.Range` (`Possible`, `Made`, `Reached`) read off the formula; `AlwaysSyntax` | `Node.invariant[T]`, `Node.invariant(stored)`, `Subject.Values/State/Answers` |
| the edges: `.refines`, `.assuming` | `graph.Edge.PartOf`, `Assumes` (`Replaces`, a decision's link, stays) | `Edge.Keeps`, `Edge.Exempt`, `.keeps`, `.exempt`; revision 14's derived premise links (R14.3) |
| the world outside | `expr.OutsideFact` (five facts), `dsl.node.OutsideSyntax`, `analysis.Premise`, `Premises` (a check), `Outsides` | `Statement.Model`, `Node.assumption(store, stored)` |
| consistency, vacuity | `core.consistency` (`Consistency`, `Group`, `Witness`, `Picked`, `Equations`, `Defining`, `Vacuity`, `Conditions`), `proof.whole.Joint`, `Possible`, `testing.search.Witnesses`, `Small`, `proof.layout.WholeModule`, `lean.lower.LowerWitness` | the contradiction search as the only guard |
| examples | `core.example.Example`, `dsl.example` (`FrFlowExamples`, `example`, `is`, `:=`), `eval.run.ExampleRun`, `OnCode`, `proof.whole.ExampleGoals`, `api.view.OnClaims` | `allows`/`forbids`, `dsl.node.Call`, `Binding`, `Examples` (node), `CallExample`, `RunExample`, `RunEnd`, `Verdict`, `Supply`, `PromiseExamples`, `CodeExamples`, `Agreement`, `ExampleResult`, `Givens`, `Probes`, `Evaluation`, `Evaluated`, `eval_i`/`probe_j`, `LeanAndScalaDisagree`, `Unproven.Examples` |
| how a claim is checked | `core.checking.Checking` (with `Evaluable`, `Shown`), `project.pipeline.Texts.checking`, `api.node.Says.checking`, `api.view.WholeView`, `Warning.NotChecked` | — |

**Three kinds of nodes.** `Statement` is `Claim(formula, reliance)`, `Assumption(formula)` or `Design(governs)`; a
node is `Node(id, says, statement)`. How a claim is checked is a function of its formula, its place and what gives
each Definition it mentions its meaning (`Checking.of`), never written beside it. What the removed kinds said is
said with these:

| What was a | Now |
|---|---|
| contract on an operation | a claim on a Definition: `Node.claim("…")(forall((held, request) => granted(held, request) === …))`. Where the formula applies one Definition to exactly its leading variables (alone, or on the left of its equation), FrFlow reads it as a call (`spec.CallForms`, derived): the post a call of the Definition's plain code is tested against. A claim that reads as no call is still a claim, tested whole (R14.5, below). |
| invariant of a type's values / of a store's state | a claim whose formula is `always[T](x => …)` / `always(stored)(s => …)` |
| a store's model | an assumption: `Node.assumption("…")(store.behavesAs(stored))` |
| a definition node (`authorized := …`) | a claim of one equation, `authorized(u, p) === grants.exists(…)`, which is also the Declaration's consistency witness; or a `define` |
| `.expects(statement)(consequence)` | a claim the expecting claim refines (`.refines(consequence)`): the consequence is the whole, proven from its parts |
| `.failsChangingNothing[E]` on a node | part of the formula: `handle(r).from(before) { … }.failsChangingNothing[Failure]` (`Ran`) |
| `.leftOpenAbove` | kept, on a claim only (`Reliance`; on an assumption it is a fault, `NodeSyntaxSuite`) |

**Two kinds of values** (§14, §15), one user type each (R14.2).
- `Declaration[A](means)`, named from its val, of any type (`val authorized = Declaration[(UserId, Path) =>
  Boolean]("…")`). It is not a `Term`: it is applied only where a statement is being written. `Node.claim`,
  `Node.assumption` and `example` take their formula as a context function `Stating ?=> Term[Boolean]`, and a
  Declaration's `apply` (and `term`) asks for a `Stating`. A `define`, a `program` and plain Scala are written
  without one, so a Declaration used by code does not compile:
  `FrFlow: a Declaration is used only in statements (Node.claim, Node.assumption, an example); code, defines and
  programs use Definitions` (`FormsSuite`). It is never implemented: the `implement…` methods and `env(d)` take a
  `Definition` only.
- `Definition[A](means)`, of any type, is a `Term`: what code and programs use. It gets its meaning once, in one
  pattern (R14.7): `.implementProven(book)(bookIfGranted)` (a define or a program; Lean proves it meets every claim
  mentioning `book`, `impl`), `.implementTested(granted)(_ => (held, request) => Calendar(held).grants(request))`
  (plain Scala, tested on generated cases against every claim mentioning `granted`), `.implementValue(d)(v)` (a
  value fixed in the model, substituted in Lean), `.implementProvided(grants, sessions)` (a value given where the code
  runs: bound by an example, drawn by a test, passed in production; Lean states every claim for every such value;
  revision 14's `provided`).
- `define { … }` and `program { … }` return a `Definition` carrying its meaning where it is written
  (`Definition.onTheSpot: Option[OnTheSpot]`, its `Code.Proven` or `Code.ProvenFlow` and its written lambda): `val
  covers = define { (b: Term[Booking], t: Term[BigInt]) => … }` is a `Definition[(Booking, BigInt) => Boolean]`,
  called by the same `apply` as any Definition (it calls the define by name, `Named.define` over its `term.Body`),
  passed where a list's operation takes a function (`held.pairwise(apart)`, `DefinitionSyntax`), and run in plain code
  by `d.fn(env)`. A meaning given twice is refused (`Fault.MeantWhereWritten`, `implementTested(isFree)(…)`),
  `implementProven` takes only a define or a program (`Fault.NotProvenCode`), and a program is the meaning of the
  Definition its claims speak of, not mentioned in a claim itself (`Fault.ProgramMentioned`; `FormsSuite`). The core
  keeps no second "Definition": a define's named body is `core.term.Body`, its vocabulary entry `core.vocab.Define`.
- What the types cannot rule out, validation does (`analysis.Meanings`): `Problem.Undefined` (a Definition nothing
  gives a meaning) and `Problem.DeclarationInCode` (a Declaration reached from proven code through a define written
  without `Stating`, e.g. by a helper that takes one as a parameter). `CodeWithoutClaim` stays.

**Two quantifiers** (§13, §15, §16). `forall` is every possible value; `always` is every value that can occur. Both
are terms (`Quantifiers.forall`, `always`), and what a statement ranges over is read off its formula (`Range.of`):
- `always[T](x => …)` (`Range.Made`): every value of `T` that can be made. Its rule is a define named as the node,
  so in Lean it is a hypothesis on every value of `T` a statement is about (`Guarded`: each `T`, each element of a
  list of them, each one a record's field holds, `RoomBookings`' bookings, and each one a world's store holds). It is
  met where FrFlow covers the code: `made_<maker>` (below) of each proven define and each store operation on its model
  whose result is a `T` (or holds one so), every run of a program writing a store whose state holds a `T`
  (`cover_<op>`), a tested Definition at its boundary (its inputs drawn meeting it, `Respecting`; its result checked,
  `Made` in `CallCheck`, `Broken.Always`), every state a store may start in (`start_<node>`). Values entering from
  outside are covered by an assumption: `outside.calls(book)` ("the outside calls `book` with values that can be
  made"). Nothing is checked at run time.
- `always(stored)(s => …)` (`Range.Reached`): every state the store reaches. Kept by every run of each program
  writing the store (`cover_<op>`, from a world meeting every `always`, given what the code relies on), from every
  state it may start in (`start_<node>`); the rule that every reached state meets it rests on four facts about the
  outside (below), each an assumption node.
- **`made_<maker>`** (R14.1; the soundness side of assuming an `always[T]` of every value): for an `always[T]` A and
  a maker whose result A's guard applies to (a `T`, a list of them, a record holding either),
  - of a proven define `d : X₁ → … → Xₙ → R`: `∀ x₁ … xₙ, H(x₁) → … → H(xₙ) → A(d x₁ … xₙ)`, given what `d`'s code
    relies on;
  - of a store operation `op` on its model (`Stored.op : P → StateM S R`): `∀ p (w : World), H(p) → H(w) → A(op_of p
    w.s)`, where `op_of p s = Id.run ((Stored.op p).run' s)` (printed beside the model, `LowerModels.resultOf`),
  each `H` every `always`'s guard on the variable (`Guarded`): a world comes with every `always` about it. Lean
  declares `A.makes_<maker>` over the maker and asks it of the code (`Prop.Makes`, `proof.terms.Making`,
  `LowerKeeps.makes`); `Required.made`. Rooms: `made_inRoom` of `roomBookingsApart` and of `endsAfterStart`, both
  proven (`Proofs.lean`).

**A claim constrains every Declaration and Definition it mentions** (`Constrained.of`, through its defines), and the
obligations follow from its formula and from what gives each Definition its meaning:

| The claim | Obligations and checks |
|---|---|
| has parts and no proven code | `complete`: its parts give it; the tries (`needed_C`, `vacuous`, `restates`, `clash`, `unsat`) |
| mentions a Definition with proven code | `impl`: the code meets it, from its parts or, without parts, from what the code relies on (`Resolved.reliesOn`) |
| mentions a Definition with plain Scala | tested on generated cases: per call when it reads as a call (`CallCheck`), else the formula evaluated whole on its drawn variables, every Definition given its meaning (`PropertyTests`, R14.5); a statement with no Scala value (a quantifier over every value of a type, in it or its defines: `Evaluable`) is "not checked" against that code, and `status` warns when nothing else checks it (`Warning.NotChecked`) |
| mentions a fixed or provided Definition | stated for that value / for every value provided |
| `always[T]` | a hypothesis everywhere; `cover_<op>`, `made_<maker>`, `start_<node>`; `inhabited_<node>` |
| `always(stored)` | a hypothesis on every world; `cover_<op>` for each writer; `start_<node>` |
| is at the bottom (no parts) | in a consistency group with the claims and assumptions sharing its open values (`consistent_<i>`) |
| has a condition `A` in `A implies B` | `satisfiable_<i>_<node>` |
| rests on the world outside | each fact listed by its `.assuming` (`Premises` checks the list: `PremiseMissing`, `PremiseNotNeeded`) |

An assumption with a formula (an outside system's promise) is trusted: a hypothesis where a proof assumes it
(`.assuming`), its adapter tested against it, and in the consistency group of its open values.

**Edges** (R14.3). `.refines(parent)` makes a part; `.assuming(x)` a premise, the one mechanism for one: an
assumption, or a claim of `always` (`PremiseNotAssumed` otherwise). The facts about the outside a check rests on are
derived (`Premises.of`), but only as a check of what the source writes: a claim whose `.assuming` misses one is
refused, naming the fact and the assumption that says it (`PremiseMissing(id, needs, by)`), and one listing an
outside fact its check does not rest on is refused too (`PremiseNotNeeded`; `BookSuite`). So a reader of
`bookWhenFree` sees `.assuming(storeModel, oneAtATime)` in the source, as today's rooms writes it, and `show` says
what each is a premise of. A fact about the outside is never a part (`OutsideAsPart`), and only an assumption says one
(`OutsideClaimed`). The root statements are the claims without parents, several allowed on any Definitions and
Declarations (§11).

**The world outside, atomicity** (§16, §17). Assumptions about the outside are expected: they reflect the company's
procedures, the outside services and how they are run, and they are reviewed as every node is. Five formulas say
them, each a term (`OutsideFact`) Lean does not state as a formula, named as today's library names them (R14.4):

| Formula | Says | The rule resting on it |
|---|---|---|
| `store.behavesAs(stored)` | the store does what its model does | code calling the store is proven on the model; `made_<op>` is proven of the model; its adapters are tested against it (`checkedAgainst`) |
| `stored.initially(held => held === Nil)` | what the state the store starts in meets (its rule a define named as the assumption) | `start_<node>`: `∀ s, initially s → A s`, what always holds of the store holds at the start |
| `stored.writtenOnlyBy(book)` | only these programs change it | every reached state is one a listed program's run leaves; a covered program writing the store and not listed is refused (`WriterNotListed`) |
| `stored.changedOneRunAtATime` | runs changing it never interleave (one process running each `atomically`, or a store serializing them) | each run is one step of the world: Lean's `f_run` and `cover_<op>` |
| `outside.calls(book)` | the outside calls `book` with values that can be made | the inputs of an entry Definition (one no code calls) meet every `always[T]` of their types |

Which facts a check rests on: a claim about a program's runs on a store, the store's `behavesAs` and
`changedOneRunAtATime`; an `always(stored)`, those and `initially` and `writtenOnlyBy`; an `always[T]`,
`outside.calls(d)` for each entry Definition whose inputs can hold a `T`, the store facts of each store whose state
can, and `behavesAs` of each store whose operations make one. Atomicity is assumed in this way, as the owner decided
(§17); asynchrony (an operator for it, atomicity assumed by default) is future work, and the README says each program
runs as one step. Rooms names its start `startsEmpty` (`initially(held => held === Nil)`): today's library's
`startsApart` (`initially(held => held.pairwise(apart))`) is being reworded by the README's builder, and an empty
start reads at a glance and also meets `endsAfterStart`'s start, which a start of apart bookings does not. The
store's boundary and model keep the names `store` and `stored` until today's library settles the distinct names it
is choosing; the rebuild takes them then.

**Consistency** (§15, §18). The statements must be proven non-contradictory: there is a meaning for every open value
under which every claim and assumption holds.
- *The groups* (`Consistency.of`). The bottom statements (stated, over every possible value, with no parts) and the
  assumptions beside them are joined while they share an open value: a Declaration, or a Definition no proof or
  fixed value gives a meaning (tested Scala, or none). Each group is one obligation, `consistent_<i>`: for every
  value provided where code runs, some meaning of each open value makes each statement true, proven code and fixed
  values standing for their Definitions. A statement with no open value is in no group: its proof is a step from what
  it rests on. Every statement above follows from its parts by a proven step (`complete`, `impl`), so it holds
  wherever they do: consistency is carried upward. Each `always` about a store gets `start_<node>`. An `always[T]`'s
  possibility is vacuity's (`inhabited_<node>`, below).
- *The witnesses* (`Witness`), derived where possible, the group solved in substitution order (R14.6): an equation
  `∀ xs, s(xs) = e` whose other side mentions no value still open gives `fun xs => e` (`Witness.Equation`; the side
  and the shape read off the IR by `Equations.defining`, the term built from the formula by the `Defining`
  transformer); a bound `s(xs) ≤ e` (or `<`, `≥`, `>`) gives the bound, or one past a strict one (`Witness.Bound`);
  each value so witnessed stands for itself in the rest, and the solving repeats until none is left; proven code is
  its own witness; a Definition only plain Scala defines is `Witness.Tested`, evidence and not proof; none is
  `Witness.Missing`, which a real cycle leaves.
- *In Lean* (`Whole.lean`, `WholeModule`): each statement in `namespace Obl`, and for a witnessed group its theorem,
  `fun sessions grants => ⟨w_access, w_signedIn, w_authorized, by frflow_witness⟩` (`LowerWitness`): the witnesses
  printed in solving order, each one given before printed where a later one mentions its value (`Printed.standing`,
  `LeanTerm`'s `standing` map), then put in the order the statement binds them. Auth's three Declarations as one
  group (`accessExactly` with its two equations at the bottom beside it): `access`'s witness is `fun u p => ((fun u
  => ∃ s ∈ sessions, s.user = u) u ∧ (fun u p => ∃ g ∈ grants, g = Grant.mk u p) u p)` (`AuthSuite`, `AuthDump.lean`
  compiled). A group with no witness is stated only.
- *Status* (`api.view.GroupStatus`): `Proven` (Lean checked the witnesses), `Evidence(tested)` (only tested Scala
  stands for some open value), `NotProven` ("consistency not proven", its own status, not a failing proof).
  `status` warns of each group not proven (`Warning.ConsistencyNotProven`); the overview counts them; each bottom
  statement's `show` says it (`Checking.Consistent`); the mechanical rule counts it as unproven
  (`Unproven.Consistency`).
- *The contradiction search* (`unsat`, `clash` tries) stays an early refuter only: proven, it shows a node wrong;
  not proven, it shows nothing, and consistency is never inferred from it.

**Vacuity** (§18). Positive statements guard against a model that says nothing (rooms' `bookWhenFree` says a free
room's request is booked and stored; `answersWhetherBooked` that booking answers whether it did), and two small
proofs more, each with a witness a search finds (`testing.search.Witnesses`: the values the knowledge base's
generators draw first, then the small values of each type, `Small`, a SmallCheck-style enumeration, each judged by
the evaluator; deterministic, at most 5,000 candidates):
- `inhabited_<node>`: some value of `T` meets an `always[T]` (rooms: `⟨(Booking.mk "" 0 1), by frflow_witness⟩`,
  `⟨(RoomBookings.mk []), by frflow_witness⟩`);
- `satisfiable_<i>_<node>`: each condition `A` of a claim's `A implies B`, with the antecedents above it and the
  variables bound above it (`Conditions`), can hold: `∃ (open values) (variables), A`. A condition no candidate meets
  is stated only, "not shown" (`VacuitySuite`). Examples may serve as witnesses but are never required.

An `always[T]` met by generated values needs its rule to have a Scala value (the search and `Respecting` judge it by
the evaluator): rooms states `roomBookingsApart` in start and end times (`pairwise(noOverlap)`), the calendar's
words, and `made_inRoom` proves it from `neverOverlap`'s moments (`apart_noOverlap`, `Proofs.lean`).

**Examples** (§18) leave the nodes. They are ordinary tests, beside the model, written as today's library writes them
(R14.4):

```scala
class GrantedExamples extends FrFlowExamples(rooms):
  example("back to back: granted"):
    granted(RoomBookings(List(Booking("Oak", 9, 10))), Booking("Oak", 10, 11)) is true

  example("overlapping: not granted"):
    granted(RoomBookings(List(Booking("Oak", 9, 11))), Booking("Oak", 10, 12)) is false
```

An example is a closed fact over Definitions and Declarations (`example(name, grants := List(…)): …` gives values
to provided Definitions); each `example` registers one as the class is built, as a test suite registers its tests
(`FrFlowExamples.examples`; a munit runner for `sbt test` is step 5's). FrFlow checks each against the code in Scala
(`ExampleRun`: `OnCode.Holds`, `Fails`, `NotEvaluated`, or `Abstract` for a fact about Declarations) and against
the claims in Lean (`example_<i>`, a try met by `frflow_example h_n … h_1`). One that sets values of provided
Definitions is not asked of Lean: `WholeView` and the snapshot show it "checked in Scala only" (`OnClaims.ScalaOnly`;
`ExamplesSuite`), so it is not mistaken for a Lean check. Nothing depends on them: the theory, its obligations and its
Lean are the same without them, no rule counts them, and consistency and vacuity never read them.

**How a reader sees how each claim is checked.** `show` prints `Says.checking` beside the statement, every line
derived (`Checking.of`, `Texts.checking`; `CheckingSuite` pins rooms'):

```
bookWhenFree          proven of book's program, bookIfGranted
                      assumed by the code calling book
                      rests on the store behaving as stored: storeModel
                      rests on one run at a time on stored: oneAtATime
grantWhenFree         proven from its parts (grantWhenNoOverlap)
                      not checked against granted's Scala: the statement has no Scala value (it quantifies over
                      every value)
grantWhenNoOverlap    tested against granted's Scala on generated cases
                      assumed by the code calling granted
                      consistent with grantWhenNoOverlap: witnessed, for Lean to check
neverOverlap          kept by every run of book, from the state it starts in
                      rests on the store behaving as stored: storeModel
                      … (one run at a time, the start: startsEmpty, who writes it: onlyBookingWrites)
endsAfterStart        met where a Booking is made (book, stored's inRoom); assumed of every Booking in Lean
                      rests on what the outside calls book with: fromTheForm
                      … (the store's four facts)
                      not vacuous: some Booking meets it
roomBookingsApart     met where a RoomBookings is made (stored's inRoom); assumed of every RoomBookings in Lean
                      rests on the store behaving as stored: storeModel
                      not vacuous: some RoomBookings meets it
oneAtATime            the world outside: runs on stored never interleave
```

A claim about tested Scala that reads as no call is "tested against granted's Scala on generated cases, the statement
evaluated whole"; one whose formula has no Scala value and that nothing else checks shows "not checked" and `status`
warns (`Warning.NotChecked`; `CheckingSuite`).

**Rooms, end to end** (`test/project/frflow/rooms/`; R14.1). The store answers a room's bookings as a domain type,
`final case class RoomBookings(bookings: List[Booking]) derives LeanType`, and what always holds of it is a claim,
`roomBookingsApart = Node.claim("A room's bookings, as the store gives them, never overlap.")(always[RoomBookings](r
=> r.bookings.pairwise(noOverlap))).assuming(storeModel, neverOverlap)`. The store's model makes it (`inRoom` is
`make[RoomBookings](held.filter(b => b.room === room))`), and `granted = Definition[(RoomBookings, Booking) =>
Boolean]` takes it. So the calendar's claims stay one equation each, over what the store can give:

```scala
val grantWhenNoOverlap = Node.claim("A request is granted exactly when it overlaps no booked time.")(
  forall((held: Term[RoomBookings], request: Term[Booking]) =>
    granted(held, request) === held.bookings.forall(b => noOverlap(b, request))))
  .refines(grantWhenFree)
```

with `roomBookingsApart` (and `endsAfterStart` of each booking held) a hypothesis on `held` in Lean (`Guarded`), and
the README's binary-search calendar is correct as stated (`Calendar.scala`, restored; named `grants`, as today's
library names it, apart from `granted`):

```scala
final class Calendar(held: RoomBookings):
  private val byRoom = held.bookings.groupBy(_.room).view.mapValues(_.sortBy(_.start).toVector).toMap

  def grants(request: Booking): Boolean =
    val room = byRoom.getOrElse(request.room, Vector.empty)
    val next = room.search(request)(using Ordering.by(_.start)).insertionPoint
    room.lift(next - 1).forall(_.end <= request.start) && room.lift(next).forall(_.start >= request.end)
```

`CalendarSuite`: on 500 generated cases meeting what always holds (`Respecting`; more than 50 of them with two
bookings of one room) it meets `grantWhenNoOverlap`; on a list the store cannot give (Oak 0–10 and Oak 1–2, a request
for 3–4) it is wrong, and that list breaks `roomBookingsApart`, so no case draws it; the README's step-4 calendar
that forgets the booking after the request is found by a generated case. `made_inRoom` proves the store's model gives
only such values, from `neverOverlap` and `endsAfterStart` of the world (`Proofs.lean`: `room_apart`).

`Rooms.scala` holds the nodes in the order they are named (so every val is set when another names it): the
Definitions `granted` and `book`, the defines `covers`, `apart`, `isFree`, `noOverlap`, the five assumptions
(`storeModel`, `startsEmpty`, `onlyBookingWrites`, `oneAtATime`, `fromTheForm`), the three claims of `always`, the
two root claims about `book` (`bookWhenFree`, `answersWhetherBooked`, each `.assuming(storeModel, oneAtATime)`), the
calendar's two claims. `Book.scala`: the store's trait, `store`, the model `Stored` and `stored`, the program
`BookIfGranted` and `bookIfGranted = program { … }`. `Knowledge.scala`:

```scala
val rooms = KnowledgeBase("Rooms")(bookWhenFree, answersWhetherBooked, neverOverlap, endsAfterStart,
  roomBookingsApart, grantWhenFree, grantWhenNoOverlap, storeModel, startsEmpty, onlyBookingWrites, oneAtATime,
  fromTheForm)
  .implementProven(book)(bookIfGranted)
  .implementTested(granted)(_ => (held, request) => Calendar(held).grants(request))
```

The root statements are `bookWhenFree`, `answersWhetherBooked`, `neverOverlap`, `endsAfterStart` and
`roomBookingsApart`. Consistency: one group (`grantWhenNoOverlap`, `granted` open, its witness the equation's right
side), and every start of the store for each `always` about it; vacuity: `endsAfterStart` and `roomBookingsApart`
inhabited. Lean (`r43-spike/rooms-lean-r15/`, `lake build` against the copy of today's `FrFlow` library with
`FrFlow/Witness.lean`; `lake-build.log`): `Dump.lean` is the rooms module as the printer gives it, `Proofs.lean`
proves `impl` of both claims of booking, `cover_book` of both `always`s about the store, `made_inRoom` of
`roomBookingsApart` and of `endsAfterStart`, and checks the three examples against the claims; `consistent_0`, the
two `start_`s and the two `inhabited_`s are proven by their witnesses or `frflow_auto`; `AuthDump.lean` adds auth's
four groups (R14.6's among them). Eighteen theorems, none using `sorry` (axioms `propext`, `choice`, `Quot.sound`);
the four rooms goldens of `test/proof/resources/rooms` are in `Dump.lean` verbatim.

**Auth's purpose over Declarations** (`test/project/frflow/auth/Auth.scala`, `AuthSuite`, `AuthExamples.scala`):

```scala
val access = Declaration[(UserId, Path) => Boolean]("whether the system lets the user reach the path")
val signedIn = Declaration[UserId => Boolean]("whether the user has signed in")
val authorized = Declaration[(UserId, Path) => Boolean]("whether the user is allowed the path, by whatever rule …")

val accessExactly = Node.claim("A user reaches a path exactly when they are signed in and authorized for it.")(
  forall((u: Term[UserId], p: Term[Path]) => access(u, p) === (signedIn(u) && authorized(u, p))))

val grants = Definition[List[Grant]]("the grant table as stored when a request is decided")
val sessions = Definition[List[Session]]("the sessions open when a request is decided")
val admits = define { (s: Term[Session], p: Term[Path]) => grants.exists(g => g === make[Grant](s.user, p)) }

val grantsAuthorize = Node.claim("A user is authorized for a path exactly when a grant names them and the path.")(
  forall((u: Term[UserId], p: Term[Path]) => authorized(u, p) === grants.exists(g => g === make[Grant](u, p))))
  .refines(accessExactly)
// sessionsSignIn (signedIn by the sessions), requestsReach (access by a session's admitted request), alike

val knowledge = KnowledgeBase("Auth")(accessExactly, grantsAuthorize, sessionsSignIn, requestsReach)
  .implementProvided(grants, sessions)
```

Each Declaration is its own group, witnessed by the equation of what refines it, for every table provided:
`consistent_0 : ∀ (grants : (List Grant)), ∃ (authorized : UserId → Path → Prop), (Auth.grantsAuthorize.claim
authorized grants)`, met by `fun grants => ⟨(fun (u : UserId) => (fun (p : Path) => (∃ g ∈ grants, (g = (Grant.mk u
p))))), by frflow_witness⟩`. With `accessExactly` at the bottom beside its two equations, the three are one group and
`access` is witnessed after them (R14.6, above). With no claim tying them to the domain (`accessExactly` alone), the
three Declarations leave their group unwitnessed: "consistency not proven". `AuthExamples` gives `grants` a value:
it holds of the code and is "checked in Scala only".

**The `&&` guideline** (§10, §16) is a style guide only: the frflow skill and the docs say a statement states one idea
and what always holds is its own `always` claim; FrFlow neither checks nor warns.

**What revisions 14 and 15 delete, add and cost.**
- *Deleted* (beside the rows of the first table): `Statement.Stated`, `Trust`, `Reading`, `Promise`, `Expectation`,
  `Subject`; the DSL's `Operation`, `Open`, `OpenTerm`, `Arity`, `Always`, `AlwaysIn`, `Modelled`, `Call`,
  `Binding`, node `Examples`, the call-form reading in `Elab` (one reading, `spec.CallForms`); `Fault.NoCall`,
  `NoRun`, `ModelClaimed`, `ExampleArity`, `OperationElsewhere`, `NotOverInputs`; `Problem.ExampleArity`,
  `DataForCodeOnly`, `FlowFailsUnstated`, `ProvenFlowTakesOutsideStep`, `ModelAsPart` (now `OutsideAsPart`);
  `TryKind.VacuousExpect`, `ObligationName.Expect`, `Eval`, `EvalImpl`, `Probe`, `ProbeImpl`, `Prop.Expected`,
  `Prop.Evaluates`, `Discharge.Evaluate`; `TermTable.expected`; `project.program.RunExamples`, `Evaluations`;
  `wire.snapshot.AgreementRow`. Revision 15: `dsl.shape.Def`, `Def1`, `Def2`, `Steps`, `dsl.example.Examples`,
  `OutsideFact.StartsWith`, `Outsides.starts`, `provided`, `startsWith`, `oneRunAtATime`.
- *Added for the user*: five outside formulas, `Declaration`, `Definition`, the `implement…` pattern
  (`implementProven`, `implementTested`, `implementValue`, `implementProvided`), `FrFlowExamples`, `example`, `is`,
  `:=`, `.failsChangingNothing` on a run. Rooms' source grows by five assumption nodes, `RoomBookings` and its
  `always`, the `.assuming` lists (one line per claim resting on the outside), and the examples file.
- *Costs.* Planned code 434 → 449 main files, 9,278 → 10,340 lines over the two revisions (revision 14: +705;
  revision 15: +357, of which `made_<maker>` and its Lean 120, whole-formula tests and "not checked" 110, the
  record guards and `Made` over records 50, the solving order and its printing 40, one Definition 20 net), 50 → 40
  `???`. Casts are in thirteen places (4.11), two new in revision 15: `Definition.called` (a define's body, at the
  curried type of its own `F`) and `Making` (a maker applied one input at a time). A guard over a record's field is
  stated in Lean only, so its selector's Scala getter is never run (`Guards`: a "FrFlow bug" throw, `Made` checking
  the field in Scala). The Lean library gains `frflow_witness` and `frflow_example` (14 lines); `check` runs the
  witness search (at most 5,000 evaluations per statement) and Lean's `Whole.lean`; the outside assumptions and their
  `.assuming` lists are reviewed like every node.

## 5. Feature audit

The full table is `r43-features.md`, with the owner's decisions applied. Every feature an example or a documented
workflow uses has a concept and stays, but for what lived only in the running service. Removed: the `runtime` module
(`service`'s checks, `checkedBy` and its `check` obligation, `checkedAtRunTime`/`RunCheck`, sampling, the assumption
watch, the reporter, `ContractViolation`), `why` on nodes, the ambient scopes (`p.value`, the fresh-variable
counter), today's `Flow` values and `Flow.effect`, content forms and `confirm --rebind`, `Retired`, filed keys as the
authority on who decides; `IDEA.md` and numbered questions (revision 2). Kept with a test and an example use each:
`race`, `guarantee`/`bracket`, `timeout`, `parTupled`, `ifM`. Changed in the user's source: `env(d)`,
`implementTested(d)(env => …)`, `knowledge.code(d)(…)` for `service`, tagless boundaries and programs, nodes without
`why`. Kept and carried in full by `testing`: property-based testing (generated cases, model-based tests, examples,
shrinking, saved counterexamples, coverage of a claim's parts, the step-refutation search). Revision 14 (owner
§10–§18, 4.14) says every feature in three kinds of nodes, two kinds of values and two quantifiers: `Param`,
`Operation` and `Open` become `Declaration` and `Definition`; contracts become claims (read as calls where they
apply their Definition to its inputs); invariants become claims of `always`; definition nodes become claims of one
equation or defines; a model's assumption becomes `store.behavesAs(stored)`; `expects` becomes a claim refined;
`allows`/`forbids` and `bind`/`bindTable` become examples beside the knowledge base (`example`, `is`, `:=`), and
`eval_i`/`probe_j` go with them. Added: the world outside's four store facts and `outside.calls`, consistency and
vacuity proven in Lean, how each claim is checked in `show`. Revision 15: `define` and `program` give a `Definition`;
`provided` becomes `implementProvided`; `startsWith` becomes `initially`, `oneRunAtATime` `changedOneRunAtATime`, a
model's examples a `FrFlowExamples` class, as today's library names them; premises are written with `.assuming`;
`made_<maker>` is asked of every maker of an `always[T]`'s values.

## 6. Rebuild plan

The new FrFlow is built from the planned core in this repository, beside today's, and replaces it once every example
runs on it. Today's modules are not changed on the way (but for one step that records their outputs), so the examples
keep working on them until each is ported.

**Layout during the rebuild.** The new modules live under `next/<module>/` with sbt ids `next-core`, …,
`next-agent`, and their own top packages (`frflow.core`, `frflow.dsl`, …). Today's `api`, `cli`, `web` and `agent`
use the same package names, so old and new modules never share a classpath: no new module depends on an old one, and
a ported example depends on new modules only. The last step moves `next/*` to `modules/*`.

**What proves the new FrFlow does what the old one did.** Step 0 records today's outputs once, as a reference
(committed under `reference/`, read by tests, never by FrFlow). Each ported example is held to four checks, run by
its `PortSuite` (in `next/project`'s tests, tagged `Lean` where it needs Lean):

1. **Proofs.** Every node the reference shows proven (a claim, contract or invariant today; a claim now) is proven by the new Lean (`status`:
   each node proven, tested or assumed as in the reference). A node whose standing differs is listed in the step's
   notes with why (a `check` obligation gone with `checkedBy`; a `let` that moved), and judged in review.
2. **Seeded bugs.** Each bug the example's suites seed today is caught: what was a `ContractViolation` at run time is
   a failing generated case or example in `check`, with its inputs (`PropertyTests`, `ModelTests`); what was a failing
   example or test is still one. The cases are listed per example below.
3. **Examples and generated cases.** Every example holds of the claims (in Lean) and of the code as in the reference; the
   property and model tests pass with the reference's seeds.
4. **Lean, as a reference.** Each generated module is compared with the reference; the differences are listed (an
   obligation dropped, a declaration reordered, a name changed) and none may weaken a statement: the new `Spec` of
   each node must state the reference's claim (checked by Lean: `example : Old.claim ↔ New.claim` for every node,
   generated by the suite, proven by `simp [frflow_defs]` or listed).

The rooms walk-through is a test of its own (`WalkthroughSuite`, step 11): it applies each change the README makes to
`examples/rooms` (steps 4, 5 and 6 of "A small app, step by step") to a copy, runs `check` and `review`, and compares
the output with the README's blocks, line by line: the failing generated case (Oak 0–4, a request 0–1), the step
refuted by a case Lean proves (Elm 2–4, a request 0–2) with "check the change to overlaps", and the claim back for
review with the changed definition of `covers`. The README is rewritten where the design changes what it says (the
run-time paragraph of step 3; `why =` in the code; step 6's "committed under the developer's name" becomes the
deciders' list), and the suite then pins the rewritten text.

**Order.** Each step is one reviewable change, green on `sbt test` (old and new) and `sbt leanTest`.

0. **Record the reference.** A `ReferenceCapture` program (in today's `check` module, a test tagged `Lean`) runs today's
   FrFlow on auth, keycloak, crm, sharing and rooms and writes `reference/<example>/`: every generated Lean module and
   proof; each node's standing (proven, tested, assumed), check status and failing examples; `tree`, `status`,
   `show` and `review` text; the rooms walk-through's three outputs (by applying its diffs to a copy); and the list of
   each suite's seeded bugs with what stops them today. Nothing in FrFlow changes. Suites: one added.
1. **`next/core`** from the planned core: names, `Ty`, `Value`, the term algebras (matching on sums, records made and
   updated, the folds, `lam`/`app`/`let`, `Either` among them) and their core interpreters (`ToExpr`, `Collect`,
   `Forward`, `PartialEval`, `Hypotheses`, `Opened`), `Expr`, `Prog` (generic in its steps' terms), `Mentions`,
   `Exprs`, `Progs`, statements (three kinds, `Written` with its term; `Range`, `CallForms`), edges, code (the five
   meanings of a Definition), `Theory`, `Validate` (any claim without parents may be a root; a node with proven code
   has as parts only claims about what it calls; every Definition given a meaning and no Declaration in code; every
   fact about the outside a check rests on said by an assumption), `Resolve`, `Callees`, `Premises`, `checking`, and
   `consistency` (the groups, the witnesses from equations and bounds, vacuity's conditions). Suites: property tests of `typeOf` (total), the `Mentions` monoid laws, `Progs.sequential`, every `Problem` (ported from `model`'s
   validation suite, its cases kept by name).
2. **`next/dsl`**: the closed `Term[A]` over final terms, the operations of today's DSL each as one algebra
   operation (the full set: today's term, list, option, set, map, tuple, match and fold operations, the `Sym`
   algebras growing with them, the list relations and runs among them), the macros (`Source.of` for text and names,
   `DataMacros` deriving records' selectors and enums once per type, `derives LeanType`, `CaseMacros` deriving each
   sum's eliminator and `make`, `valName` for every name, `Implication` refusing an unparenthesised chain), defines
   called by name (each a `Definition` carrying its `core.term.Body` of `lam`s, to six inputs), `Declaration` (with
   `Stating`) and `Definition`, the three node forms without `why` (`Node.claim`, `Node.assumption`, `Node.design`; a program's claim
   as a run from a world with its failure clause, ids the vals' names as written, `.refines`, `.assuming`,
   `implies`, `when(…)(…).otherwise(…)`), `forall` and `always` (`always[T]`, `always(stored)`), the outside's
   formulas (`behavesAs`, `initially`, `writtenOnlyBy`, `changedOneRunAtATime`, `outside.calls`), examples as tests
   (`FrFlowExamples`, `example`, `is`, `:=`), `Implementing` (`implementProven`, `implementTested` with `env =>
   code`, `implementValue`, `implementProvided`), `Elaborate`; `Flow`, `Recorded`, `Recording`,
   `ReadRecording`, `Boundary` (named from its val), `BoundaryOps` derived (`recording`, `call`, `lifted`, `model`;
   `derives BoundaryOps`), `Model`, `ModelState`, a model declared with its instance of its boundary's trait
   (`store.model(…)(Stored(_))`, read as `stored.in(world)`, checked by `checkedAgainst`) and assumed by
   `Node.assumption(…)(store.behavesAs(stored))`, `Clock`. Suites: `RecordingSuite` (every combinator),
   `NodeSyntaxSuite`, `NestedHelperSuite`, `FormsSuite`, `CrmClaimsSuite`, `SharingClaimsSuite`, `RunsSuite`;
   `model`'s node, term and flow suites ported (their cases kept by name, flows rewritten as tagless programs). Every
   node of the five examples is written in the three kinds here, before any example is ported: each contract as a
   claim, each invariant as a claim of `always`, each definition node as a claim of one equation or a define, each
   `allows`/`forbids` as an example, each model and procedure the code rests on as an assumption.
3. **`next/proof`**: obligations as `Prop` over terms (`impl` written: a node with proven code is proven from its
   parts by it, `complete` not asked of it; `cover_<op>`, `made_<maker>`; the whole theory's `consistent_<i>`,
   `start_<node>`, `inhabited_<node>`, `satisfiable_<i>_<node>` and `example_<i>`, with `WholeModule`,
   `LowerWitness` and the Lean library's `frflow_witness` and `frflow_example`), `LowerModels` (the boundaries, their models and `World`, each program's
   run on them), the Lean AST, `LeanTerm` (every term printed from itself, each
   define once: the only printer of terms), lowering of the structure around terms (programs' blocks, propositions,
   declarations, constants), printing, layout (`RefutesModule` included), proof-file rules, judges. Law suites: the
   printed Lean reads back and prints the same (`PrinterLawsSuite`, in the planned code), and, with `lake` in the
   suite, Lean decides each generated term's printed Lean as the evaluator evaluates it. Suites:
   `CrmModulesSuite` and one module of every kind; a test per try kind; a test per proof-file rule; `lean`'s obligation
   suites ported.
4. **`next/eval`**: `Evaluate` (the only evaluator of terms), `Semantics`, `Literals`, `Reflect`, `DefSyntax`,
   `CodeSyntax`, `Running`, `CallCheck`, `Wiring`, `ExampleRun`, `FlowInterpreter` over `World`s. Suites:
   `model`'s eval and example suites ported; `RunningSuite`; `TermLawsSuite` (a written lambda run on arguments
   equals the evaluator's value; folding keeps values; the generated terms reach every algebra); the outside
   vocabulary's suite; a law suite: a
   program's recording run on the models gives what `Running` gives on the models' instances.
5. **`next/testing`**: `Draw`, derived generators, `PropertyTests` (shrinking, coverage, saved counterexamples),
   `ModelTests` (an adapter against `World.models`, as `StoreModelSuite` does on rooms), `Interleavings`,
   `search` (`StepRefutation`, `Small`, `Witnesses`). Suites: `model`'s testing suites ported, with today's seeds; a
   `Gen` monad law suite; `SmallSuite`.
6. **`next/decision`**: content, ledger, `Deciders`, payload, review, rules. Suites: `ledger`'s decide and standing
   suites ported over `Subject`; `DecidersSuite`.
7. **`next/wire`**: the snapshot's rows, the codecs of the ledger, the deciders' list, checks and tests. Suites: a
   round trip per file.
8. **`next/project`**: algebras with in-memory interpreters and law suites (`ProjectFiles`, `Lake`, `Git`,
   `LedgerStore`, `KeyRing`), programs, `Analysis`, contents and subjects, fingerprints, configuration. Suites:
   `check`'s suites over the in-memory interpreters; those needing Lean tagged.
9. **`next/api`**: the three algebras, the views (`WholeView`, `Says.checking`), `FrFlowApi.inMemory`. Suites:
   `api`'s suites ported.
10. **`next/cli`, `next/web`, `next/agent`** on the new API, with `init` writing the first deciders' list. Suites:
    `cli`'s and `agent`'s suites ported; the web view's smoke test.
11. **Port rooms** (root claims about the `book` program, the calendar's claims, a store with its model and SQLite
    adapter, plain code, a proven program, generators; owner §9–§18). Source changes, as `test/project/frflow/rooms/`
    has them: no `why`; three kinds of nodes and two kinds of values (`granted` and `book` Definitions, `book` given
    its meaning by `implementProven(book)(bookIfGranted)`, `granted` by `implementTested(granted)(_ => (held,
    request) => Calendar(held).grants(request))`, the README's binary-search calendar); the store answering a room's
    bookings as a `RoomBookings`, which `granted` takes; booking as two claims (the store after, one equation; the
    answer, one equation); `always(stored)` for never overlapping, `always[Booking]` for ending after starting,
    `always[RoomBookings]` for a room's bookings never overlapping; the calendar's claims one equation each over what
    the store can give; five assumptions about the outside (the store's model, its start, its one writer, one run at a
    time, the form's requests), each claim resting on one listing it with `.assuming`; the examples in
    `RoomsExamples.scala`, a `FrFlowExamples` class (`BookSuite`, `AlwaysSuite`, `CalendarSuite`,
    `ConsistencySuite`, `ExamplesSuite`, `CheckingSuite`, and the Lean of `r43-spike/rooms-lean-r15`, whose
    obligations, `made_inRoom`s, consistency, vacuity and examples are proven); the SQLite adapter checked by
    `stored.checkedAgainst(start = …, observe = …)`, its `inRoom` answering a `RoomBookings`. `PortSuite(rooms)` and `WalkthroughSuite`. The README's
    walk-through rewritten (no run-time paragraph; reasons in decisions; the deciders' list; each program runs as one
    step, assumed by `oneAtATime`) and pinned. New ledger: the owner decides its nodes.
12. **Port auth, then keycloak, then crm**, one change each.
    - auth (327 lines): its `Param`s become Declarations (`access`, `authorized`, `signedIn`: the purpose, abstract)
      and Definitions (`grants`, `sessions` provided where the code runs; `admit` tested Scala); its definition nodes
      claims of one equation, each its Declaration's consistency witness, the group solved in substitution order
      (`test/project/frflow/auth/Auth.scala`; its `User` and `Resource` opaque sorts again, `Opaque`);
      `decisionContract` two claims on `admit`, one idea each, its `allows`/`forbids` examples; `p.value` → `env(d)`;
      `Server` calls `knowledge.code(admit)(…)`. Seeded bug: `careless` (today a `ContractViolation`) is a failing
      generated case of the claims on `admit`.
    - keycloak (718 lines): assumptions about operations with adapters (`sessionLookup`, `storeKeepsState`); its
      `checkedBy` and that node's `check` obligation go. Seeded bugs: `dropping` (a store that drops a write) and
      `leaky` (introspection leaking another realm's session) are failing generated cases of `StoreKeepsState` and
      the introspection claim.
    - crm (1,362 lines): `Database[F, T]` tagless, the expiry job a program `Expiry[F[_]: Flow]`, its model an
      instance over `Model`, `SqliteDatabase` and `MemoryDatabase` adapters `Database[IO, Id]`; four `checkedBy`
      removed. The expiry job gains its `ifM` (saving only when something expired), with its claim still proven.
      `noCrossTenantRead`, today an invariant of answers kept through views, becomes a claim `forall` over the
      read Definitions it relates, and its `.exempt`s go (a claim mentions only what it constrains): the test of a
      root statement over two Definitions (owner §11).
      Seeded bugs: `leaky` and `relabel` (the read claim), the SQL bug (`WHERE` dropped: a failing case of the
      adapter against `storedMatching`, as today's `buggy.test` already shows), `careless` (writes), `dropping`
      (`StoreEdits`), each a failing case or model test in `check`.
13. **Port sharing** (3,247 lines, the largest): `LibraryStore`, `Mailer` and the clock tagless; the HTTP handler,
    housekeeping and notifications as programs; 58 `why` texts offered as the first decisions' reasons. The kept
    combinators get their uses here, each under a claim that is proven: notifications' delivery bounded by
    `timeout(clock)` and raced against the next tick (`race`); housekeeping's lease taken and released with
    `bracket` (`guarantee`); the handler loading the library and the invitations at once (`parTupled`, with its
    `commute_i`). `HousekeepingOnTime` loses "the server checks it as it runs". Seeded bugs: the fault sweep and
    interleavings suites, with today's seeds.
14. **Remove today's modules.** Delete `modules/{model,protocol,lean,ledger,check,api,cli,web,agent}`, move
    `next/*` to `modules/*`, drop the `next-` ids, point `bin/frflow` and `build.sbt` at the new modules, delete
    `reference/` once the last `PortSuite` has passed on the final layout. Rewrite `docs/USAGE.md` (no run-time
    section; `env(d)`; tagless boundaries; the deciders' list; reasons in decisions; three kinds of nodes, two kinds
    of values, `forall` and `always`; the world outside as assumptions, each program one step, asynchrony future
    work; examples as tests; consistency and vacuity), `docs/DAG.md` (§4 snapshot, §5 decisions), `docs/index.html`,
    the frflow skill (several root statements, on any Definitions, relating them if need be, kept to a concise few by
    the agent: owner §11; one idea per statement, a style guide, §10, §16), and the scala-fp skill's examples. Tighten the architecture
    test to the target edges and the size baseline to zero violations.
15. **The owner decides the new ledgers.** With his key the only entry of each example's `.frflow/deciders`, he
    accepts each example's nodes (`confirm` takes the mechanical ones; the reasons offered from the old `why` texts),
    and commits the ledgers and lists. Nothing an agent signed before counts.

**The planned code's stubs, and the step that writes each** (40 `???` in 31 files; each one's parts are written
and tested, so a step fills in, it does not redesign):

| Step | Stubs |
|---|---|
| 2 (`next/dsl`) | `BoundaryMacros.derived` (`derives BoundaryOps`; rooms' `BookingsOps` is written by hand as it will make it); `Reify` of maps, sets, worlds |
| 3 (`next/proof`) | `Required.feasible`, `Required.commutes` and `LowerProp`'s commutation (today's `commute_i`); `made_<maker>` of a program's result (a run's outcome; a define's and a store operation's are written); `WholeModule.of`, `NodeModules.of`, `RootImplModule.of`, `VocabularyModules.of`, `RefutesModule.of` (each module's declarations are written, `LeanDump` lays them out); `LowerValue` of maps and sets; `LowerProg`'s `raise`, `catch`, `collect`, `accumulate`; `LeanOutput.diagnostics`, `usesSorry`, `ProofRules.theorems` |
| 4 (`next/eval`) | `FlowInterpreter`'s loops, `collect`, `accumulate`, `catch`, `raise`, `ParEach`; `Literals` and `Reflect` of maps, sets, tuples, outcomes, worlds; `CodeSyntax.code` and `running` (production's `knowledge.code(d)(…)`, over `Wiring`) |
| 5 (`next/testing`) | `ModelTests.of` (a store's realizations against its model, over `ModelTests.run`); `StepRefutation.candidate`; derived generators (a `Draw` of `Gen.Derived` by the type's `DataRep`: the suites write theirs by hand); shrinking; a munit runner of `FrFlowExamples` for `sbt test` |
| 6 (`next/decision`) | `Reading.waitsFor`, `Meaning.decisionMoved`, `Below.movedOnlyWith` (ported from `ledger`) |
| 8 (`next/project`) | `ProjectFiles.make`, `LedgerStore.file`, `inMemory`, `Lake.make` (the interpreters); `NodeChecker.proven`, `stamp`, `CheckPlan.levels`; `Lexer.blankComments`, `collapseSpaces`; `Texts.implementation`, `model`, `implementations` |
| 9 (`next/api`) | `FrFlowApi.make`, `Views.tree`, `Views.inbox` |

**Seeded bugs, and what catches each after the port.**

| Example | Seeded today | Stopped today by | Caught after the port by |
|---|---|---|---|
| auth | `careless` decision code | `ContractViolation` on the call | a failing generated case of the claims on `admit` |
| keycloak | `dropping` store | `ContractViolation` (the read-back check) | a failing generated case of `StoreKeepsState` |
| keycloak | `leaky` introspection | `ContractViolation` | a failing generated case of the introspection claim |
| crm | `leaky` read | `ContractViolation` | a failing generated case and example of the read claim |
| crm | `relabel` read | failing examples | failing examples (unchanged) |
| crm | SQL `WHERE` dropped | `ContractViolation` at `RecordsByQuery`, and its generated tests | its generated tests against `storedMatching` |
| crm | `careless` write | `ContractViolation` | a failing generated case of the write claim |
| crm | `dropping` database | `ContractViolation` at `StoreEdits` | a failing generated case of `StoreEdits`, and the model test of the database |
| sharing | fault sweep, interleavings | the generated runs | the same, over the recorded programs on the adapters |
| rooms | the README's three changes | `check`, review | `check`, review (`WalkthroughSuite`) |

**Risks.**

| Risk | Likelihood | Effect | Mitigation |
|---|---|---|---|
| a lowering differs from today's printer where the examples rely on it | medium | a proof that went through no longer does | the reference Lean and the per-node `Old.claim ↔ New.claim` check; the authored proofs are ported with the example |
| two FrFlows in one build for most of the rebuild | certain | a longer build; a fix made twice | `next/` gets no feature today's code lacks; today's code gets fixes only |
| tagless programs read differently from today's `Flow` values (sharing's 3,247 lines) | medium | the port of sharing is long | sharing last, with the combinators' uses; the recording's tests per combinator before |
| the closed `Term` and the macros cost compile time on a large model (4.13: +0.2 s, 1.3 times, on rooms from clean; none on sharing's largest match file) | medium | slower edits of big models | the operators built through one helper (`Term.both`); the macros (`make`, the eliminators) only where written; a type's `LeanType` derived once (`derives`); measured again on each example as it is ported |
| a derivation or macro expanded at every use passes the JVM's limits (a method's 64 KB, a class's constant pool) | seen, then fixed | a model that compiles today does not | revision 9's inline `LeanType` given did so on sharing's largest file; derivation is now once per type, and the spike compiles that file in every step's build (step 2 on) |
| names from the val: renaming a val renames its node | certain, by decision | the node is reviewed again under its new id, its old id gone | `review` shows the rename as a gone node and a new one with the same content, so the decider sees it is a rename; the old decision's reason is offered |
| a claim reads as a call only where it applies its Definition to its leading variables | low | a claim meant as a call is tested as a whole formula instead | `show` says how each claim is checked (`Checking`), so the reading is seen; `FormsSuite` |
| a claim about tested Scala has no Scala value (it quantifies over every moment) | certain on rooms' root words | its code is not tested against it | `show` says "not checked against …", and `status` warns when nothing else checks it (`Warning.NotChecked`); rooms proves `grantWhenFree` from its parts |
| an `always[T]`'s rule has no Scala value | medium | generated values cannot be drawn meeting it | state it in evaluable words (rooms' `roomBookingsApart` in start and end times) and prove the link (`made_inRoom` from `neverOverlap`) |
| no witness is derived for a consistency group (an open value whose equation mentions another open value) | medium | "consistency not proven" shown for a sound theory | a status, not a failure: the author adds an equation, a fixed value or a proof; the derivation grows with the examples' groups |
| the facts about the outside are many to write | certain | each knowledge base with a store gains its assumptions (rooms: five) | each is a sentence a reviewer can judge, the rules resting on it are derived and shown, and a missing one is named with what to say (`PremiseMissing`) |
| an outside vocabulary needs an interpreter FrFlow ships to know it natively | low | it runs through its meaning in the core, correct but less direct Lean | the meaning in the core is required, the native instance optional, and a law ties them |
| a bug only production data shows, which the run-time check would have caught | certain in principle | the bug reaches production | the owner's decision; the model and property tests' seeds include the examples' worlds and saved counterexamples |
| the examples' decisions are lost | certain, by decision | every node decided again | the old `why` texts offered as reasons; `confirm` batches the mechanical ones |
| the macros (`Data`, `BoundaryOps` over `B[_[_], _[_]]`, `Source.of`) meet a case the examples lack | medium | an elaboration error, or a wrong signature | errors are `ElabError`s naming the site; `BoundaryOps` tested on each example's boundary |
| rewriting 5,176 lines of FrFlow tests lets a case slip | medium | a behaviour unpinned | each ported suite keeps its case names; a step lists the cases it drops, with why |

## 7. Rules that keep it from decaying

1. **Module graph in `build.sbt` only** (4.3). A new module or edge is an architecture change, approved first.
2. **`ArchitectureSuite`** (munit, in the `project` module's tests): scans `modules/*/src/main` imports and package
   clauses; fails on a package edge not in `project/architecture.conf`, on any package cycle within a module, on
   `private[frflow]`, on `ThreadLocal` anywhere, on these imports from `core`, `dsl`, `proof`, `decision`:
   `cats.effect`, `io.circe`, `java.nio.file.Files`, `scala.util.Random`, `System.getenv`; and on
   `java.util.concurrent.atomic`, `cats.effect.std.Mutex` or `synchronized` outside `eval.Running` and
   `eval.flow.FlowInterpreter` (the concurrent run's lock). About 150 lines.
3. **scalafix `DisableSyntax`** on `core`, `proof`, `eval`, `decision`, `dsl`: no `null` (allow-list:
   `dsl.node.Parent.of`), no `var` in classes, no `throw` (allow-list: "FrFlow bug" sites; a `Failure(fault)` in
   `Elab`, `ReadRecording` and `Term.select`, placed by `Elab`; `NotEvaluated` in `ValuesSyntax.apply`,
   `Applied.called`, `Running.value`, `DefSyntax`, and `Evaluate.lam`, caught back into `Left` by its `app`), no
   `asInstanceOf` outside the places 4.11 names (in `eval.term`, only through `Fn.as`, in `param`, `free`,
   `part` and `fails`), no `isInstanceOf`, no `@unchecked` outside `eval.Fn`.
4. **Size budgets** in CI against a committed baseline (`budget.py`): a change may not add a violation.
5. **Golden files** for every example's Lean, contents, CLI output and the README walk-through, made from the new
   FrFlow once each example is ported (step 11 on); a change to them is listed in its commit message and approved.
6. **Law suites** for every instance (`checkAll` with cats-laws: `Gen`, the monoids, `Deferred`) and every algebra
   (against each interpreter); `Flow`'s two interpreters agree on the models.
7. **A new feature names its concept.** The pull request template asks: which of the fifteen concepts it extends (or
   the theory of the new one, in two sentences), which IR case or algebra operation it adds, which interpreters handle
   it (Lean, Scala, tests, content, view), which example uses it, which golden files change.
8. **Review checklist** (`.claude/skills/scala-fp/references/review-checklist.md`), plus: no analysis reads printed
   Lean or source text; no view stores what a function of `View` computes; no `Option` field that a kind decides; no
   ambient state; nothing in production checks a call; a new pattern is added to 4.10 with its example file, or not
   used; a name says what it is, once per concept, and a comment says only what the name and the types do not.
9. **The owner's core concepts stay the only ones** (owner §15). `ArchitectureSuite` pins the cases of `Statement`
   and `NodeKind` (claim, assumption, design), of `ValueKind` (Declaration, Definition) and the quantifiers
   (`forall`, `always`); a change to them is an owner's decision, and a feature is said in them, never beside them
   under another name.

## 8. Where each problem is addressed

| Problem | Addressed by |
|---|---|
| P1 no IR | terms as algebras with interpreters (`core.term`), one printer and one evaluator of them; the IR made by one of them and read only by the analyses (`core.expr`, `Written`), `Exprs.mentions`; programs recorded into `Prog` (steps 1, 2) |
| P2 string Lean | `proof.lean` AST, `LeanTerm`/`Printed` for terms, `LowerProg`, `LowerProp` over `TermTable`, `Prop`; the printer's read-back law; `Scope` on types (steps 1, 3) |
| P3 `Node` | `Statement` cases, edges, positions, attachments apart; no `why`; the run-time wrapper gone, the example runner in `eval` (steps 1, 2, 4) |
| P4 `KnowledgeBase` | `Theory` (5 fields), `Resolved`, `testing.Settings`; no wiring or reporter in it (steps 1, 2, 5) |
| P5 core → wire | `wire` depends on the domain (step 7) |
| P6 ledger on `SnapNode` | `Subject`, `Standings`, `Shown` (steps 6, 8) |
| P7 cycles, visibility | a top package per module, the architecture test (steps 1 to 10, 14) |
| P8 duplicates | one `Ty`, one `TestReport`, one `Shown`, one `OpSig`, one content form, one fingerprint, `Walk` in core |
| P9 casts | `Value` literals; typed algebras (an interpreter of terms casts only where `Evaluate` reads the untyped values it is given, through `Fn.as`); sums matched by derived eliminators and outside vocabularies found by typed keys, no type test; casts in the places 4.11 names |
| P10 ambient state | none: binders named by the interpreter that binds them (HOAS), values passed to plain code, recordings numbered in their own `State`; `BoundaryOps` and `Data` derived and lambda names read at compile time; explicit `Env`; `Hits`; config read once |
| P11 raw-text content | one `Content` form without source text; the simple lexer's fingerprint; `Governance`, `RelPath` (steps 6, 8) |
| P12 flattened views | `NodeView` by concept, `Placement` by relation, `Tally`, the snapshot by kind (steps 7, 9) |
| P13 thrown model errors | `Fault`, `ElabError`, `Problem`, `ValidatedNec` (steps 1, 2) |
| P14 effects | algebras with in-memory interpreters (step 8) |
| P15 surface width | the owner's audit: run-time features removed, combinators kept with tests and uses (steps 2, 13) |
| P16 golden only on fixtures | the reference (step 0), each example's `PortSuite`, then goldens of the new FrFlow (step 11 on) |
| P17 two statements of the purpose | `IDEA.md` removed, `README.md` ordinary prose, reasons in signed decisions (steps 11 to 15) |

## 9. Changes in this revision

Revision 15 answers review round 14 (`r43-review-14.md`: R14.1–R14.8) and holds the owner's §15 concepts strictly.
The planned code compiles with `-Werror` from clean and its 147 tests pass (`sbt clean compile proof/test
decision/test dsl/test project/test evaluation/test testing/test`: 21, 7, 11, 88, 18 and 2; `r15-sbt.log`);
`budget.py` finds no line over 120 columns, no file over 200 lines, no parameter list over four, every package within
its size (the facade's one file allowed), and over 20 lines only the four matches over an enum. Lean 4.35.0 builds the
rebuilt rooms and auth modules (`r43-spike/rooms-lean-r15`: eighteen theorems, no `sorry`).

| Finding | What changed |
|---|---|
| R14.2 (blocking) one user type for a Definition | `define { … }` returns a `Definition[A => R]` (`Definition[(A, B) => R]`, …) and `program { … }` a `Definition[A => Program[R]]`, each carrying its meaning (`Definition.onTheSpot`: `Code.Proven`/`ProvenFlow`, its written lambda, a define's `Body`), called by `Definition.apply`, passed as a function by `DefinitionSyntax`, run by `d.fn(env)`. `dsl.shape.Def`, `Def1`, `Def2`, `Steps` are deleted; the core's `term.Definition` is `term.Body` (a define's named body), `vocab.Define` its vocabulary entry. A meaning given twice (`MeantWhereWritten`), `implementProven` of a non-define (`NotProvenCode`) and a program named in a claim (`ProgramMentioned`) are faults. `FormsSuite`. 4.14. |
| R14.3 (major) premises written | `.assuming(…)` is the one mechanism: rooms writes `bookWhenFree.assuming(storeModel, oneAtATime)`, `neverOverlap.assuming(storeModel, oneAtATime, startsEmpty, onlyBookingWrites)`, as today's rooms does. `Premises.of` only checks the list: `PremiseMissing(id, needs, by)` names the fact and the assumption saying it, `PremiseNotNeeded(id, premise)` an outside fact listed that the check does not rest on; `show` reads the written edges (`Outsides.assumed`). `BookSuite`. |
| R14.1 (major) the calendar over what the store can give | `RoomBookings derives LeanType` with `roomBookingsApart = Node.claim(…)(always[RoomBookings](r => r.bookings.pairwise(noOverlap)))`, made by the store model's `inRoom` (`make[RoomBookings](…)`), taken by `granted`; the calendar's claims stay one equation each, the `always` (and `endsAfterStart` of each booking held: guards now reach a record's fields, `Guards`, `Made`) a hypothesis on `held`; the README's binary-search calendar restored (`Calendar.grants`). `made_<maker>` written (`Required.made`, `Making`, `Prop.Makes`, `LowerKeeps.makes`, `LowerModels.resultOf`), its formula in 4.14; rooms' two `made_inRoom`s proven. Generated tests: `PropertyTests.of` written (per call, and whole), `CalendarSuite`. |
| R14.4 names of today's library | `FrFlowExamples(kb)` classes with `example(name): fact`; `stored.changedOneRunAtATime`; `stored.initially(rule)` (`OutsideFact.Initially`, `start_<node>` as `∀ s, initially s → A s`); `.assuming` written; rooms' `storeModel`, `onlyBookingWrites`. The start is `startsEmpty` (today's `startsApart` is being reworded; an empty start also meets `endsAfterStart`'s); `store`/`stored` kept until today's library settles its distinct names. |
| R14.5 tested whole formulas | `Checking.TestedAgainst(d, whole)` and `NotTested(d)` by `Evaluable`; `PropertyTests.of` evaluates a claim reading as no call on its drawn variables, every Definition given its meaning; "not checked" and `Warning.NotChecked` for a claim nothing checks. `CheckingSuite`. |
| R14.6 witnesses in substitution order | `Consistency` solves a group repeatedly, each witnessed value standing for itself in the rest; `LowerWitness` prints the witnesses in solving order, each earlier one substituted (`LeanTerm`'s `standing`), then in binding order. Auth's three Declarations as one group: `access` witnessed. `AuthSuite`, `AuthDump.lean` compiled. |
| R14.7 one `implement…` pattern | `provided` is `implementProvided`. |
| R14.8 the size | 449 main files, 10,340 lines (+357), 40 `???`, each with its step (6). |
| open questions | examples setting values show "checked in Scala only" (`OnClaims.ScalaOnly`, `Rows.example`; `ExamplesSuite`); crm's `noCrossTenantRead` is step 12's test of a root over two Definitions; auth's sorts opaque again in step 12. |

Revision 14 applies the owner's core concepts (`r43-owner-changes.md` §10–§18) to the design and the planned code,
strictly: no removed kind survives under another name. The planned code compiles with `-Werror` from clean and its
135 tests pass (`sbt clean compile proof/test decision/test dsl/test project/test evaluation/test testing/test`: 21,
7, 11, 76, 18 and 2; `r14-sbt-final.log`); `budget.py` finds no line over 120 columns, no file over 200 lines, no parameter
list over four, every package within its size (the facade's one file allowed), and over 20 lines only the four
matches over an enum. Lean 4.35.0 builds rooms' and auth's modules with the whole theory's obligations and the
examples (`r43-spike/rooms-lean-r14`: fourteen theorems, no `sorry`).

| Owner's decision | What changed |
|---|---|
| §15 three kinds of nodes | `Statement` is `Claim(formula, reliance)`, `Assumption(formula)`, `Design(governs)`; `NodeKind` three; `Node.claim`, `Node.assumption`, `Node.design` the only forms. Deleted: `Node.contract`, `Node.invariant`, `Node.definition`, `Statement.Stated`, `Trust`, `Reading`, `Subject`, `Promise`, `Expectation` and `.expects`, `Edge.Keeps`, `Edge.Exempt`, the invariants of answers. How a claim is checked is derived (`core.checking.Checking`, `Texts.checking`, `Says.checking`). `FormsSuite`, `CheckingSuite`. 4.1, 4.4, 4.14. |
| §14, §15 two kinds of values | `Declaration[A]` (not a `Term`; applied only under `Stating`, which only a statement's or an example's formula gives; a Declaration in code does not compile, "FrFlow: a Declaration is used only in statements …") and `Definition[A]` (a `Term`, given its meaning once: `implementProven`, `implementTested`, `implementValue`, `provided`; `define` on the spot; `Code.Proven`, `ProvenFlow`, `Tested`, `Valued`, `Provided`). `Problem.Undefined`, `DeclarationInCode`. Deleted: `Operation`, `Open`, `OpenTerm`, `Arity`, `Code.ProvenBeside`, `Choice`. `FormsSuite`, `AuthSuite`. |
| §15 a claim constrains every value it mentions; obligations from its formula and meanings | `Constrained.of`; the call reading derived (`CallForms`: `Call`, `Run` with its failure clause), never a kind; the obligations table of 4.14 (`complete`, `impl`, tests per call or whole, `cover_<op>`, `made_<d>` planned, `start_<node>`, `inhabited_<node>`, `consistent_<i>`, `satisfiable_<i>_<node>`). `RoomsSuite`, `BookSuite`. |
| §13, §15 `forall` and `always` | `always[T](x => …)` and `always(stored)(s => …)` (`AlwaysSyntax`, `Quantifiers.always`), what a statement ranges over read off its formula (`Range`); the rule a define named as the node, a hypothesis everywhere (`Guarded`), kept by every writer (`cover_<op>`), met at the start (`start_<node>`), checked where a tested Definition makes a value (`Broken.Always`). `AlwaysSuite` (was `InvariantSuite`). |
| §11 several roots; `.refines`, `.assuming` | Roots are claims without parents; a premise is an assumption or a claim of `always`; `OutsideAsPart`, `OutsideClaimed`. `BookSuite`. |
| §16, §17 the world outside, atomicity | Five formulas (`OutsideFact`): `store.behavesAs(stored)`, `stored.startsWith(…)`, `stored.writtenOnlyBy(…)`, `stored.oneRunAtATime`, `outside.calls(d)`, each said by an assumption node; which a check rests on derived (`Premises`), a missing one refused naming what to say (`PremiseMissing`), a writer left out refused (`WriterNotListed`), each listed by `show`. Atomicity assumed by `oneRunAtATime`; asynchrony future work. Rooms' five assumptions (`Outside.scala`). `BookSuite`, `CheckingSuite`. |
| §18 consistency | `core.consistency` (`Consistency.of`: groups of bottom statements and assumptions sharing an open value; `Witness`: `Equation`, `Bound`, `Tested`, `Missing`; `Equations`, `Defining`), `proof.whole.Joint` (`consistent_<i>`, `start_<node>`), `WholeModule`, `LowerWitness`, the tactic `frflow_witness`; `GroupStatus` (`Proven`, `Evidence`, `NotProven`), `Warning.ConsistencyNotProven`, `Unproven.Consistency`, `Checking.Consistent`; the contradiction search an early refuter only. `ConsistencySuite`, `AuthSuite`; Lean compiled. |
| §18 vacuity | `Vacuity.Inhabited`, `Satisfiable` (`Conditions`: each condition of `implies` with what is bound and assumed above it), `proof.whole.Possible`, witnesses found by `testing.search.Witnesses` over the generators and `Small` (at most 5,000 candidates), "not shown" otherwise. `VacuitySuite`, `SmallSuite`. |
| §18 examples | Examples leave the nodes: `Examples(kb)(example(name, d := v)(fact))`, `is`; checked against the code (`ExampleRun`, `OnCode`) and against the claims in Lean (`example_<i>`, `frflow_example`); nothing depends on them. Deleted: `allows`/`forbids`, `Call`, the required `forbids`, `CallExample`, `RunExample`, `Verdict`, `Supply`, `Givens`, `PromiseExamples`, `CodeExamples`, `Agreement`, `Probes`, `Evaluation`, `eval_i`/`probe_j`, `LeanAndScalaDisagree`, `Unproven.Examples`. `ExamplesSuite`, `ExampleRunSuite`. |
| §10, §16 the `&&` guideline | A style guide only (the frflow skill and the docs); nothing checks or warns. |
| auth's `authorized` | A Declaration with its consistency witness from `grantsAuthorize`'s equation, for every grant table provided (`test/project/frflow/auth/Auth.scala`, `AuthSuite`, `AuthDump.lean` compiled); without the equation, "consistency not proven". User and Resource are concrete (`UserId`, `Path`) in the planned code. |
| rooms end to end | `Rooms.scala`, `Book.scala`, `Outside.scala`, `Calendar.scala`, `Knowledge.scala`, `RoomsExamples.scala`; `Dump.lean` and `Proofs.lean` built by `lake` (`impl` twice, `cover_book` twice, `consistent_0`, `start_` twice, `inhabited_endsAfterStart`, `example_0` to `example_2`). 4.13, 4.14. |
| Costs | 448 main files, 9,983 lines (+705), 42 `???` (−8); four casts more (4.11); the Lean library gains two tactics. 4.11, 4.14. |

Revision 13 answers review round 12 (`r43-review-12.md`: R12.1–R12.3) and applies the owner's rule of one idea per
statement and several roots (`r43-owner-changes.md` §10, §11). The planned code compiles with `-Werror` from clean and
its 115 tests pass (`sbt clean compile proof/test decision/test dsl/test project/test evaluation/test testing/test`:
21, 7, 11, 57, 18 and 1; `r43-review13-sbt.log`); `budget.py` finds no line over 120 columns, no file over 200 lines, no parameter
list over four, and over 20 lines only four matches over an enum. Lean 4.35.0 accepts the printed rooms module and
proves its four obligations (`r43-spike/rooms-lean`).

| Finding or decision | What changed |
|---|---|
| R12.1.1 `before(stored)`, near-names | `stored.in(before)` (`ModelState.in`; the world `apply` is gone). The model is declared with its instance, `val stored = store.model("every booking the store holds, oldest first")(Stored(_))` (`ModelSyntax`, a `StoreModel[Bookings, List[Booking]]`; the model types in their own package, `dsl.model`), so the names are `Bookings`, `store`, `Stored` (only the model's class), `stored`; the assumption is `Node.assumption(stored)("…")`. `BookSuite` (posts printed, models golden), `InvariantSuite`. |
| R12.1.2 the Boolean `fold` | `when(c)(a).otherwise(b)` (`Conditional`; Lean's `if`), `Term[Boolean].fold` removed (its uses in `Flow.timeout`, `Generated` and sharing rewritten); an option's and an either's folds stay. The root's store equation uses it; `BookSuite` prints it as `if … then … else`, the term laws run it. |
| R12.1.3 no form for an adapter check | `stored.checkedAgainst(start = held => …, observe = memory => …)` (`AdapterCheck`), run by `ModelTests.run`: both made holding a state, generated calls (`Runs`, from the boundary's signature, values through `Respecting`) on each, the first call answered differently (`Difference.Answer`) or the state read back when it differs (`Difference.State`). `StoreModelSuite` writes exactly this; the hand wiring is gone. Tests: agrees; a store forgetting the room filter found at `inRoom`; one forgetting to add found by its state. |
| R12.1.4 an assumption's edge called `.refines` | `Edge.Assumes(node, premise)`, written `bookWhenFree.assuming(storeAsModelled)`: beside the order, so `parts`, `impl`, `PartNotCalled` and the view's `Part` leave it out (the view gains `Assumes`/`AssumedBy`); `Problem.PremiseNotAssumed` (a premise that is not an assumption) and `ModelAsPart` (a model refining a node); `PartNotCalled` reads parts, not children, and `Callees.promises` no longer lets a model through. `BookSuite`. |
| R12.1.5 two contract shapes | One: `Node.contract(op)(statement)(formula)`. `NodeMacros` and the inferred form are deleted; `Node.contract("…")(…)` fails to compile with "a contract names its operation first: `Node.contract(op)("…")(forall(…))`". Elaboration's checks (`OperationElsewhere`, `NotOverInputs`, `NoRun`) do what inference did. Every contract in the tests names its operation. `ContractFormSuite`, `CrmContractsSuite`. |
| R12.1.6 two names per node | A node's id is its val's name as written (`Head.make` without `capitalize`), in reports and Lean (`Rooms.grantWhenFree.claim`). `ContractFormSuite`, `BookSuite`, `InvariantSuite`. |
| Owner §10 one idea per statement | `Node.invariant[Booking](statement)(b => …)` (a data invariant) and `Node.invariant(stored)(statement)(held => …)` (a state invariant): `Statement.Invariant(subject: Subject, rule, holds)`, its rule a define named as the node; a root statement, never a part. Lean: every variable of a statement comes with the invariants' hypotheses (`Guarded`, a transformer of `forall`/`exists`; `Guards` builds each from the variable's `Ty`: a value, a list's elements, a world's store); a contract whose code is a program is asked `cover_I` for each invariant of a state it can change (`Prop.Keeps`, `Keeping`, `LowerKeeps`: `I.keeps_op`, from a world meeting every invariant, given what `impl` is given). Scala: a data invariant is checked where a value is made (`Made` in `CallCheck`: an example's inputs, an allowed example's result; `Broken.Invariant`), and generated values meet it (`Respecting`). Today's relation of answers (crm's `noCrossTenantRead`, kept through views) stays, as `Subject.Answers` with `Edge.Keeps` and `Kept`; for the two new kinds who keeps what is derived (`Scope.keeps`), `Exempt` applies to all (`ExemptOutsideScope` new); a call is checked against both through `CallInvariant`. Rooms: `bookWhenFree` one equation over the store (`stored.in(after) === when(isFree(held, request))(held :+ request).otherwise(held)`); book's Boolean answer is its own statement, `answersWhetherBooked` (`booked === (stored.in(after) =!= stored.in(before))`), the two being the contract of `book` said one idea per statement (both root statements, owner §11; each proven of `bookIfGranted`); `neverOverlap` on the store's model; `endsAfterStart` on `Booking`; `grantWhenFree` and `grantWhenNoOverlap` one equation each, with no hypothesis written (`wellFormed` is gone). `InvariantSuite`, `BookSuite`, `RoomsSuite`, `StoreModelSuite`. 4.1, 4.4, 4.6, 4.13. |
| Owner §11 several roots | The one-root law is replaced: `Refinement.roots` is every claim, contract and invariant without parents, on any operations, relating them if need be; `Validate` raises only `NoRoot` (`SeveralRoots` and its same-operation exception are deleted); `View.roots` and `Snapshot.roots` are lists; the frflow skill's rewrite (plan step 14) says to keep them a concise few. Rooms keeps booking's two statements; its root statements are those two and the two invariants. `BookSuite`: a contract on `granted` with no parent and a claim relating `book` to `granted` validate beside booking's statements. 4.1, 4.5, 4.6, 4.13, 6. |
| R12.2 rooms' goldens never compiled | `r43-spike/rooms-lean/`: the rooms module as the printer gives it (`Dump.lean`: the defines, `Boundaries.decls.lean`, the program lowered from its recording, `bookIfGranted_run`, the claims, the two `keeps_book` declarations, `impl` of both statements of booking, `cover_neverOverlap`, `cover_endsAfterStart`) builds with `lake` against a copy of today's `FrFlow` library: the `Prop`-valued result (`Booking → World → (Prop × World)`) and the program's `if` on a `Prop` need only `open Classical`, which the preamble has. All four rooms goldens are in it verbatim, so they stay goldens. `Proofs.lean` proves the four obligations (axioms `propext`, `choice`, `Quot.sound`). Found and fixed: `LowerProg` had no case for `atomically` (a transaction is its body on the models); and `cover_I` was first stated without `impl`'s hypotheses, which the proof showed it needs. 4.11. |
| R12.3 what `lifted` makes | 4.13: for `Bookings[IO, Id]`, a `Bookings[IO, Term]` whose methods evaluate each argument's term to its value (`Terms.value`, the running program's evaluator), call the adapter, and make each result a term again (`Terms.term`, by its `LeanType`); nothing checked. `BookingsOps.lifted` is now written so (no `???` left in it), and `StoreModelSuite` runs `BookIfGranted` in `IO` over `Running` on the in-memory store lifted: a free request booked, a clash not. |

Revision 12 answers review round 11 (`r43-review-11.md`: R11.1–R11.3). The planned code compiles with `-Werror`
from clean and its 106 tests pass (`sbt clean compile proof/test decision/test dsl/test project/test
evaluation/test testing/test`: 21, 7, 11, 48, 18 and 1); `budget.py` finds no line over 120 columns, no file over
200 lines, no parameter list over four, and over 20 lines only four matches over an enum.

| Finding | What changed |
|---|---|
| R11.1 the store's model was not written, elaborated or printed | The model is an instance of the boundary's trait over its state, `final class Stored[F[_]: Flow](state: Model[F, List[Booking]]) extends Bookings[F, Term]` (`inRoom` filters by room, `add` appends with `:+`, new), taken by `Node.assumption(store, stored)(Stored(_))(…)`. `Nodes.assumption` reads it into a `StateModel` (`BoundaryOps.model`, `ReadRecording.steps`), declared with the `BoundarySig` (`Declarations.boundary`); `Elaborate.vocabulary` puts both in the vocabulary. `LowerModels` prints the `Boundaries` module's declarations and a program's run (`f_run`): rooms' as golden files in `BookSuite`, and crm's `Boundaries.lean` and `expireOnce_run` byte for byte from `CrmModels` (they were hand-built in the test). In Scala, `World.models` runs a call as its model's steps (`FlowInterpreter` gains `Modify`); `StoreModelSuite` runs an in-memory store against it with `ModelTests` on 200 generated runs, and finds a store that forgets to filter by room. Programs and models read `map`/`flatMap`/`for` on any `Flow` (`FlowSyntax`); the recording `Flow` is in `Recorded`'s companion. 4.13, 6. |
| R11.2 the boundary's name written twice | `Boundary[Bookings]("the SQLite table the bookings are kept in")`, named from its val; its `BoundaryOps` the given `derives BoundaryOps` will make (rooms gives `BookingsOps` in `Bookings`' companion). 4.13 says what each `BoundaryOps` member makes for a trait. |
| R11.3 `impl` without parts | Documented (`Required.impl`, 4.1): a node with proven code and no parts is a leaf, so its hypotheses are what its code relies on, the contracts on the operations it calls through its defines, wherever they sit. `ImplSuite`: crm's `ExpiryJob` under a root claim, its code `expireOnce`, gets `∀ U, h_SharesExpire → ExpiryJob.claim[runExpiry := expireOnce_run]`, the obligation today's `Spec.lean` states, with its sentence (now naming `expireOnce_run`, as today's does). |

Revision 11 answers review round 10 (`r43-review-10.md`: R10.1–R10.3) and applies the owner's root for rooms
(`r43-owner-changes.md` §9). The planned code compiles with `-Werror` from clean and its 102 tests pass
(`sbt clean compile proof/test decision/test dsl/test project/test evaluation/test testing/test`: 20, 7, 11, 45,
18 and 1);
`budget.py` finds no line over 120 columns, no file over 200 lines, no parameter list over four, and over 20 lines
only four matches over an enum.

| Finding or decision | What changed |
|---|---|
| R10.1 a flow statement as the root, proven from what its code calls | `Refinement.roots`: any stated node without parents but an assumption (a claim, an invariant or a contract). `Callees` (what a node's proven code calls, through its defines; `f_run` for a program). `Required.impl` written: "∀ U, H → claim[op := code]", `H` the node's parts or, without parts, the contracts of what the code calls; `complete` is not asked of a node with proven code. `Validate.code`: `CodeWithoutPromise`, and `PartNotCalled` for a child that is neither a promise about what the code calls nor the model of a boundary it calls (`definitions` written too: `DefinedTwiceIn`, `DefinesAnOperation`). `Statement.Model(model, boundary)` and `Node.assumption(store, stored)`; `implementProven` written (a program's code is `ProvenFlow`); `Elaborate.vocabulary` written (every define, closed over the defines they call, and each program's `f_run`); the recording `Flow` found in `Recorded`'s companion, and `program`'s types inferred from its lambda. Rooms (`Book.scala`, `Knowledge.scala`): `BookWhenFree` on `book`, refined by `GrantWhenFree` and the store's model, `implementProven(bookWhenFree)(bookIfGranted)`; `BookSuite`: the one root, a stray part refused, `complete` of the calendar's claim and not of the root, no `idle`, and its `impl` as Lean. The idle try makes none for a flow root (`canDoNothing` is false for a program; said in `Idle`). 4.1, 4.4, 4.6, 4.13, 6. |
| R10.2 a missing `derives LeanType` | `@implicitNotFound` on `LeanType`: "Plain is not a domain type yet: add derives LeanType to its declaration" (code quoted), tested in `ContractFormSuite`. The ambiguous-given error after a body that does not type stays: Scala 3 has no `@implicitAmbiguous` (4.13). |
| R10.3 a failure clause restated the formula | One run with both outcomes, `op(a).from(before) { … }.failing { … }` (`Ran`); `Elab.run` reads the success side as the post, `Elab.failure` the failing side as the failure clause, `Opened` opening the side asked for. `.onFailure` deleted; `.failsChangingNothing[E]` kept. 4.13 says the combined form is the one to use. `SharingContractsSuite`. |

Revision 10 answers review round 9 (`r43-review-9.md`: R9.1–R9.8) and applies the owner's names (`Operation[F]`,
`Open[A]`). The planned code compiles with `-Werror` from clean and its 98 tests pass (`sbt clean compile
proof/test decision/test dsl/test project/test evaluation/test testing/test`: 20, 7, 11, 41, 18 and 1); `budget.py` finds no line
over 120 columns, no file over 200 lines, no parameter list over four, and over 20 lines only four matches over an
enum.

| Finding or decision | What changed |
|---|---|
| R9.1 a contract relating two operations on the same inputs | `Node.contract(op)(statement)(formula)` names the operation; inferred as before when one is applied to the variables. The abort says how to name it (`… name the one it is about, \`Node.contract(save)(…)(…)\``). `OperationElsewhere` applies to the named operation only; the other is an ordinary mention. crm's `SaveWrite` and sharing's `CanViewContract` (four inputs: `Operation.apply`, `CallShape` and `forall` written to four) in `test/project/frflow/crm`, `…/sharing`, with their Lean (`CrmContractsSuite`, `SharingContractsSuite`); `ContractFormSuite`: two operations need naming, named the other is a mention. 4.4, 4.13. |
| R9.2 flow contracts had no claim form | `Worlds.runs` and `fails` (a run's outcome and world after bound by host functions), in every interpreter; `Program[R]` in `core.term` (Scala's `World => (Either[Any, R], World)`); `runExpiry(now).from(before) { (result, after) => … }`, `.failing { (error, after) => … }`, `before(databaseModel)` (`ModelState`). `CallShape.program` opens the input and the world before, `Elab.run` checks the run (`Fault.NoRun`) and `Opened` opens it, so the post is over `(now, result, before, after)`. `ExpiryJob` written so prints byte for byte as the hand-built `ExpiryIr.post` and as `ExpiryJob/Spec.lean`; `HandleContract` with `.failsChangingNothing[Failure]` and a failure clause written as a claim (`.onFailure`); `RunsSuite` evaluates, prints and initializes a run. `Expr.Runs` replaces `Expr.RunOn`. 4.13. |
| R9.3 `implies` groups to the left | `implies` is a macro (`Implication`) refusing a chain whose left operand is an `implies` not written in parentheses, with the message saying which groupings to write; the 4.13 table writes `h1 implies (h2 implies c)`. `ContractFormSuite`. |
| R9.4 names | `allows`/`forbids` take `returning =`; `dsl.node.Case` is `Call`; a case without fields is matched as `.on(Change.Clear)(…)` (`Changes.scala`, the generator). |
| R9.5 `Param` | `Operation[F]` (an `Arity[F]` required at compile time) and `Open[A]` (not a function's type), the owner's names, in `dsl.vocab` with `Opaque`; `Open`, the design's own word for an open term, avoids `example.Given`. |
| R9.6 the owner's list relations | `Lists.nodup` and `Lists.pairwise` (two binders), `xs.allDistinct`, `xs.pairwise(apart)` or with a lambda, printed `(List.Nodup xs)` and `(List.Pairwise (fun (a : A) (b : A) => …) xs)`; `xs.forall(endsAfterStart)` with a define. Rooms now uses all three, as today's `Knowledge.scala`; `RoomsSuite` prints and runs them; the generator covers them. |
| R9.7 spike reporting | Re-measured (load average about 3 on four cores from other sessions' builds; none of this session's): rooms and sharing's largest match file (its 26 matches, cut down to compile alone in both). Revision 9's derivation by an inline given re-derived a type's structure at every use: sharing's file passed the JVM's method and class size limits. A domain type now `derives LeanType` once. Table in 4.13, with the first clean run read correctly. |
| R9.8 evaluator and IR loose ends | `Undefined` deleted: `lam` throws `NotEvaluated` (the documented edge, 4.6) and `app` catches it; tested that a function value used outside fails with it and inside gives `Left`. `foldEither` notes both its types, `foldLeft` its accumulator's (tested on variables that note nothing). `Expr.Proj` deleted, `Expr.RunOn` replaced by `Expr.Runs`, which `ToExpr` makes. `Prop.Formula` holds the `Written` formula, and `LowerProp` reads its IR instead of rebuilding it. |
| Found while revising | `StepRefutation.answerOf` still read a post's last input as the result: it now finds `op(inputs) === e` in a claim-form post (tested on rooms). |

Revision 9 answers review round 8 (`r43-review-8.md`: R8.1–R8.10) and applies the owner's forms (`r43-owner-changes.md`
§6). The planned code compiles with `-Werror` from clean and its 81 tests pass (`sbt clean compile proof/test
decision/test dsl/test project/test evaluation/test testing/test`: 20, 7, 11, 26, 16 and 1); `budget.py` finds no
line over 120 columns, no file over 200 lines, no parameter list over four, and over 20 lines only four matches over
an enum.

| Finding or decision | What changed |
|---|---|
| R8.1 two back ends per concern | The owner took the first fix. `Prop.Formula` holds a `Stated[Boolean]` and `Prop.Commutes` a `Prog[Stated[?]]`; `Prog` is generic in its steps' terms (`Prog[Expr]` for the analyses by `Progs.map`). `Printed` (over `LeanTerm`) is the only printer of terms, `Evaluate` the only evaluator; `LowerProg`, `LowerProp` and `LowerObligation` lower only the structure around terms; `Semantics` runs formulas, lambdas and programs' terms by `Evaluate`. Deleted: `Lower`, `LowerIterate`, `LowerPrim`, `LowerMaps`, `LowerPattern`, `Denote`, `DenotePrim`, `Compiled`. The IR is read only by the analyses in 4.13's table. Printer law: `PrinterLawsSuite` (print, read with `LeanReader`, print gives the same text; folded first, the same and never longer; split, the whole is the term; an obligation's formula printed by the term printer; the reader refuses what the printer cannot write). `CrmModulesSuite`'s spec and obligations now print from terms. 1, 4.1, 4.3, 4.11, 4.13. |
| R8.2 hard constructs had no algebra | `Sums.cases` with arms as `When` (a derived `Case`'s test, its fields bound as HOAS variables; the eliminator derived per type from `Mirror.SumOf` by `CaseMacros`, no cast), `Records.construct`/`copy` (`make[R](…)`, `x.updated(_.field, v)`), `Lists.foldLeft`, `Options.foldOption`, `Eithers` (`left`, `right`, `foldEither`), `Functions.let`; each in `ToExpr`, `Evaluate`, `LeanTerm` (and passed through `Forward`, `Collect`). `ChangesSuite` prints and runs each on the rooms model; the generator (`Slot`, `Generated`) makes all of them and `TermLawsSuite` checks it reaches every algebra. 4.13. |
| R8.3 the README's forms | Names from the val: a node's id is its val's name capitalized, a `Param`'s and an `Opaque`'s the val's name (`Source.valName`); renaming a val renames the node (`ContractFormSuite`, `RoomsSuite`). `implies` replaces `==>`, binding last (`TermLawsSuite`). A contract is written exactly like a claim: `NodeMacros.contract` finds the one `Param` applied to exactly the formula's variables, `Opened` makes the post; the lambda form is gone (`RoomsSuite`, `ContractFormSuite`). `.refines(parent)` replaces `.under`. `Param` → `Operation[F]` (and `Given[A]` for open values) proposed for the owner to confirm. 4.4, 4.13. |
| Owner §6: `allows`/`forbids` | `allows(…, result = r, "label")` and `forbids(…)` replace `expect`/`reject` (`Verdict.Allows`, `Forbids`); `Rooms.scala` uses them and `RoomsSuite` checks their verdicts. |
| R8.4 arity families | `Functions.lam`/`app` and one `Named.define`/`param`: a define is a `Definition[F]` whose body is a `lam` per input, called one argument at a time; `ToExpr` flattens applications, `LeanTerm` prints them flat, `Evaluate` applies host functions (`Fn.curried` at the values boundary). `Named.applied1…6`, `call1…6`, `Definition1…6`, `Final1…6` deleted; the user's `define { (a, b) => … }` with several inputs stays (`Def1`, `Def2`, `DefineShape`, `Param.apply`). 4.13. |
| R8.5 notes cost | Notes are on the term where they arise (`Annotations.noted`) and gathered once by the `Collect` interpreter; no operation merges notes, the sentinel variable and the second build of each body are gone. Transformers keep their information across `noted`. 4.13. |
| R8.6 the outside-algebra lookup | `Sym.extension[E[_[_]]](key: Ext[E]): Option[E[T]] = None`, overridden by an interpreter that knows `E` (matched on the key's singleton type: no cast, no unchecked test); transformers forward none and so run the meaning. `CountSuite`: a transformer over an interpreter that knows `count` runs its meaning. 4.13. |
| R8.7 casts | `TermLawsSuite`: a bound variable run by another interpreter fails loudly. 4.11 corrected: `Evaluate` casts through `Fn.as` where it reads the untyped values it is given (`param`, `free`, `part`). |
| R8.8 `Dup` | Deleted with its test; 4.13 says why no product interpreter is needed. |
| R8.9 repetition | `Terms.over` for `all`, `any`, `filter`; `Term.one`, `both`, `app` and the binder helpers make each `TermSyntax` operation one line; `PartialEval.constant` takes the literal's maker from each fold (no type test, no dead fallback); the phase `project.program.Evaluate` renamed `RunExamples`. |
| R8.10 laws | Generators cover the R8.2 operations (`Slot.Kind`), with a coverage test; the printer's read-back law (R8.1). The Lean-decides law waits for `lake` in the suite (step 3). 4.13. |
| Spike | The HOAS-body mistake (`held.forall(b => b.start)`) added: the same message before and after. Compile time measured again on the owner's forms with examples: 0.88 s today, 1.23 s planned (median of 8 clean compiles; the machine was shared). 4.13. |
| Found while testing | `NotOverInputs` reported the inputs left, not the operation's (fixed, tested); `True`/`False`, which `Term`'s doc named, were missing (added). |

Revision 8 answers review round 7 (`r43-review-7.md`: R7.1–R7.10) and applies the owner's decision on terms
(`r43-owner-changes.md` §5, `tagless-brief.md`). The planned code compiles with `-Werror` from clean and its 61 tests
pass (`sbt clean compile proof/test decision/test dsl/test project/test evaluation/test testing/test`: 20, 7, 11, 10,
12 and 1); `budget.py` finds no line over 120 columns, no file over 200 lines, no parameter list over four.

| Finding or decision | What changed |
|---|---|
| R7.1 proven-only operations not wired | `Wiring.operations` takes an operation's Scala code or else its proven define, compiled from its IR by `Denote` (revision 9: run from its term by `Semantics`) (`runs`, `proven`); `WiringSuite`: a tested operation calling a proven-only one needs nothing supplied, and the wired one answers. 4.3. |
| R7.2 compile-time numbering covered only top-level lambdas | Resolved by the tagless decision: binders are host functions, named where an interpreter binds them; nothing is numbered before. `NestedHelperSuite`: the helper nested in itself prints two names, has two variables in its IR, and runs correctly. 4.8.B, 4.13. |
| R7.3 a deciders list could be replayed | The signed bytes of a list name the list before it (`Deciders.after`, the predecessor's `ref`); `follows` requires it and `committed` requires the whole chain to link. `DecidersSuite`: a list committed again after a later one removed a decider does not restore it. 4.9. |
| R7.4 `injected` dropped a finalizer after a shared `let` | `injected` recurses through `Prog.Let`; `RecordingSuite`: a raced branch ending in a shared `let` keeps its side of the result. |
| R7.5 `VarId` packing | `VarId.written` and `apply` deleted; `VarId.level` (a binder's depth) and `VarId.step` (a recording's step, negative). 4.1 (3). |
| R7.6 `Elab.rebinds`' third case a comment | `rebinds` deleted with the numbering (4.13). |
| R7.7 `each`, `raise`, `handle` were `???` | Written in `Recording` (`Recorded.Each`, `Recorded.Handle`), `ReadRecording` (`Prog.Loop`, `Prog.Catch`, `Prog.Raise`) and `Running`; `RecordingSuite` tests each, `RunningSuite` raises and handles. |
| R7.8 production's concurrency untested | `RunningSuite`: two programs at once under `atomically` lose no update. The interleavings stay on the recorded `Prog` (the object Lean proves); 4.12 says which interpreter runs what. |
| R7.9 `Interleavings` rebuilt each example per run | `Examples.runs` builds each example's run once; `Interleavings` replicates only the runs. |
| R7.10 the facade exported `Running` | `Running` has a private constructor, is made by `make`, and is no longer exported; users reach it through `knowledge.running[F](…)` (`CodeSyntax`). |
| Terms in tagless-final style (owner, §5) | `core.term`: ten algebras bundled as `Sym[T]`, `Final[A]`; interpreters `ToExpr` (the IR, kept in `Written` for the analyses), `Evaluate` (`d.fn`, `Running`), `LeanTerm` (the Lean printer, by scope), `Hypotheses`, `PartialEval` (over `Forward`), `Dup`; HOAS binders; the closed `Term[A]` (one cast, `Term.bound`); records' selectors derived by `DataMacros`; defines as named `Definition`s called by name (`Def1`, `Def2`, `Steps` for programs); `Count` outside the core; `TermLawsSuite`, `RoomsSuite`, `CountSuite`; the spike in `r43-spike/`. Each choice cites LNCS 7470 or CKS. 1, 3, 4.1, 4.8.A, 4.8.B, 4.10, 4.11, 4.13, 6. |

Revision 7 applied the owner's decisions on revision 6 (`r43-owner-changes.md` §2, and his clarification that
property-based testing stays in full). Its planned code compiled with `-Werror` and its 41 tests passed. Its rows on
decisions A and B below are superseded by revision 8's (terms final inside; no numbering).

| Owner's decision | What changed |
|---|---|
| D. Ground-up rebuild in the same repository; today's Lean a reference | Section 6 is a rebuild plan: new modules under `next/` in dependency order (steps 1–10), the examples ported smallest first (rooms, auth, keycloak, crm, sharing; steps 11–13), today's modules deleted at the end (step 14). Equivalence is shown per example by its `PortSuite` against a recorded reference (proofs, seeded bugs, examples and generated cases, Lean compared claim by claim) and by `WalkthroughSuite` for the README's rooms walk-through. 1, 4.8.D, 6. |
| G. Fresh ledgers | One content form; `Format`, `Formats`, `Retired`, `Rebinding`, `Command.Rebind`, `Warning.OldForm` deleted; `CodeFingerprint` has one form; `Payload` is the new ledgers' own. The owner decides each example's ledger once it is ported (step 15), with the old `why` texts offered as reasons. 4.8.G, 4.9. |
| A. Terms concrete for the user, initial IR inside | Kept as designed; no interpreter of terms in user code. The tagless boundaries keep `T = Term` in programs for this reason. 4.8.A, 4.8.C. |
| B. No ambient state | `Fresh` and the ambient `Values` deleted. Variables numbered at compile time (`AsWritten.id`, `VarId.written`; `Fault.LambdaInItself` for a lambda nested in itself; `NumberingSuite`); a recording's steps numbered in its own `State` (`VarId.step`). Plain code given its values: `core.code.Values`, `Impl.make: Values => AnyRef`, `implement(c)(env => …)`, `env(p)` (`ValuesSyntax`), `d.fn(env)`, `Env.of(values)`. `Param.value`, `Fault.ValueReadWhileBuilding`, `Captures` deleted. 4.3, 4.8.B. |
| C. Tagless boundaries | `dsl.flow` rewritten: `Flow[F]` (a `Monad` with the combinators), `Recorded` and `Recording` (Lean's interpreter), `ReadRecording` (to `Prog`, a bound term shared as a `let`), `Boundary[B[_[_], _[_]]]` with `BoundaryOps` (recording, called by name, lifted adapter, model), `Model[F, S]`, `Clock[F, T]`, `program { … }`; `eval.Running` (production's interpreter, `F: Async`); `FlowInterpreter` runs a recorded `Prog` on a `World` (models or adapters); `Flow.effect`, `Bound`, `FlowRun` deleted. `RecordingSuite`, `RunningSuite`. 4.3, 4.8.C. |
| E. Twelve modules (thirteen less `runtime`) | `runtime` deleted from the build and the graph; the facade moved to `eval`; `testing` split into `testing` and `testing.report`. 4.3. |
| F. The simple lexer's fingerprint | `CodeFingerprint(sha)` by `ScalaTokens` over `Lexer`; no raw-text form. 4.8.F, 4.9. |
| No run-time checking | `runtime` removed with `checkedBy` (`Promise.check`, the `check` obligation), `checkedAtRunTime`/`RunCheck`, sampling, the assumption watch, the reporter, `ContractViolation`, `WiringError`, `Denote.impl`, the run-time views and fields. 4.12 says what this removes and simplifies, and where each check went: the call check is `PropertyTests` over `CallCheck` and `eval.run.Wiring` (moved from `runtime`), an adapter is tested against its assumption and its model (`ModelTests`); two things are no longer caught once code is deployed (an adapter's bug only real data shows; a deployed value breaking a fact about it). `knowledge.code(c)(…)` is `service` without the check. `PropertyTestsSuite`. |
| Property-based testing stays in full (clarification) | `testing` carries it: `PropertyTests` (generated cases, the values a call reads made by `Wiring`, judged by `CallCheck`, shrinking, saved counterexamples, coverage), `ModelTests` (implementations against models, over `World`s), `Interleavings`, `StepRefutation` (today's refutation search, with `proof.layout.RefutesModule`). 4.1 (11), 4.3. |
| Flow combinators: keep all | `race`, `guarantee`, `bracket`, `timeout`, `parTupled`, `ifM` are `Flow` methods with `Prog.Race` and `Prog.Guard` (each with its sequential reading); one test each in `RecordingSuite`; a use each in crm (`ifM`) and sharing (the rest), step 12–13. |
| A committed, developer-signed list of who may decide | `ledger.Decider`, `Deciders` (`follows`, `committed`, `counts`); `KeyRing.deciders` read from `Git`'s committed versions; `DecideProgram` refuses an unlisted key first (`Refusal.NotADecider`); `Warning.DecidersUncommitted`, `NotADecider`; filed keys (`publish`, `filedName`) deleted. `DecidersSuite`. 4.8, 4.9. |
| Nodes have no `why` | `Prose` deleted; `Node(id, says, statement)`; `Node.claim(id, statement)(…)`; no `why` content field; `Says.reason` from the binding decision. 4.4, 4.5, 4.8. |

What changed since the measurement (2.6) is folded in: `testing.StepRefutation` and `RefutesModule` for the step
refutation, `Cause.movedUnderCode`, and the deciders' list going beyond keys counted as committed.

Revision 6 answered round 5 (R5.1–R5.4): every operation with code wired for a service, adapters included; what the
examples bind required at wiring; the mutable state named; a code-only symbol never typed `Unit`. The run-time half of
it is removed in this revision; `Wiring` (now `eval.run.Wiring`, for tests and `knowledge.code`), `Statement.givens`
and `Problem.DataForCodeOnly` stay.

Revision 5 answered round 4 (R4.1–R4.6): `enforce` and `checkExamples` written as small functions with their tests
(`checkExamples`'s stay; `enforce`'s became `PropertyTests`' judgement in this revision); the mechanical rule as
today's, through `ReadProof` and `Unproven`; `Rows` writing each case itself; `Promise.withExamples` and the contract
instances in `OnContract`'s companion; both problems of an exemption; `VocabularySuite`.

Revision 4 answered round 3 (R3.1–R3.14): `Texts.vocabulary` as today's field, pinned against auth's ledger; the
failure clause's post in a flow contract's claim terms; `examples` on assumptions about an operation over
`OnPromise`, `leftOpenAbove` over `OnContract`; `TermTable` computed once and passed on; every flow the developer's
code builds in a `Fresh` scope; `Obligation.doc` made where the obligation is; `CallShape` and `DefineShape`; the
snapshot as `wire`'s own rows with one mapping; `split` left out of the snapshot; `LowerProp.evaluates` reading the
`Value`; `NotAllowed.LemmaImport`; the invariant problems; `Forall(about, body)`.

Revision 3 answered round 2 (R2.1–R2.23): the node views filled in by concept and the snapshot by kind; `LowerProp`,
`TermTable`, the invariant scope on types, the `V2` contents and the subjects written, with `impl` and `unsat` lowered
from `Prop` byte for byte; today's proof-file rules, one case each; a design's parents in its own meaning; one error
shape (`Fault` placed as `ElabError`); shared lowering helpers; no budget wrappers; one naming convention and one name
per concept; one flow interpreter, sequential or concurrent; typed run-time terms; named state; defines named at
compile time and declarations kept for `Validate`; the rule gaps closed; steps 12 and 13 merged.

Revision 2 answered round 1 (R1.1–R1.26) and applied the owner's changes: `IDEA.md` removed as a concept, the README
ordinary prose, no numbered questions, old `IDEA` entries read and kept by `Retired`; the plain-code path placed in
the module graph; production flows run directly; a Lean AST reproducing crm's files; obligations with `Iff` and
evaluations as an input; `Shown` per piece; flow and function contracts and examples apart; signatures over today's
payload; a layout-keeping fingerprint with `confirm --rebind`; review with rewording; a rule per command; streamed
checks; views without `Analysis`; the readability rules (short definitions, few patterns, short comments).

Revision 1: first full version (architecture map, sources, target with planned core code, feature audit, plan,
rules).

