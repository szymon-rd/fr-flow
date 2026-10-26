# Using FrFlow

The reference for the CLI and what it checks. The [README](../README.md)
explains the idea; [DAG.md](DAG.md) is the design.

FrFlow is in two layers. [FrFlow (core)](#frflow-core) is the method and its tools: the DAG, the proofs, the decisions,
the CLI and the web view, used by a developer with no AI. [With an AI agent](#with-an-ai-agent) is a layer on top,
which a project enables, for an agent that proposes the nodes and writes the code and proofs.

## FrFlow (core)

### Running

Requirements: JDK 17+, sbt, and Lean 4.35.0 (`lake` on the `PATH`, or
`FRFLOW_LAKE`). `bin/frflow PROJECT COMMAND` runs a project's CLI
(`bin/frflow auth tree`), compiling with sbt on first use and after a change.
`--help` lists the commands.

Tests: `sbt test` runs the fast ones (about a minute). The tests that run Lean end to end (tagged `Lean`, several
minutes) run with `sbt leanTest`; `sbt testAll` runs both, as before a merge.

### Commands

| | command | what it does |
|---|---|---|
| read | `tree [NODE]` | the DAG from the root (or below NODE): status, kind and state, statement |
| | `show NODE`, `diff NODE` | a node in about a screen (`--full`: all of it); what changed since it was decided |
| | `inbox`, `find WORDS\|PATH` | what waits, then the summary; where a change belongs |
| decide | `review` | decide what waits, parents first: `[a]ccept [r]eject [s]kip [v]iew [q]uit` |
| | `accept NODE...`, `reject NODE`, `confirm`, `revisit NODE`, `gone NODE` | one decision, with `-m REASON`; confirmed on a terminal, `--yes` without one |
| prove | `render`, `check [NODE]`, `scaffold NODE` | Lean and `.frflow/kb.json`; prove what changed; proof stubs for what is left open |
| | `status`, `ci` | the tree, the summary and the warnings; exit 1 unless complete (`ci` checks first) |

`--as NAME` names who decides (default: `FRFLOW_AS`, or the name the key is
filed under). The commands that decide, and the web view, ask for it when neither is
set.

`accept IDEA` accepts `IDEA.md` (see below); `IDEA` is not a node id.

The web view is not a command: it is an sbt task, `sbt "PROJECT/serve [--port N] [--as NAME]"`
(see [Web view](#web-view)).

### Starting a project

1. `sbt "frflowInit NAME"` sets up an empty project in `examples/NAME`: a knowledge base with no nodes, its main
   object, its Lean project, and its line in `build.sbt` (then `sbt reload`).
2. The developer writes `IDEA.md`: what the system is for, in prose, in sections.
3. `IDEA.md` waits for the developer, first in `inbox` and `review`: they accept it (`accept IDEA`, signed, or in the
   web view). The root is decided after it.
4. The developer writes the root, then its parts, each naming the section of `IDEA.md` it comes from (`idea = "..."`),
   and decides each in turn.

Later, a change to `IDEA.md` brings it back for review, and the root waits for it again. A change to what a section
says brings back the nodes that name that section.

### Output and exit codes

On a terminal the output has colors and Unicode and fits the terminal's width:
formulas, diffs and decisions wrap, other lines are cut (`show --full` shows them
whole). `--plain`, `NO_COLOR` or `TERM=dumb` turn this off. Off a terminal (CI,
agents, a pipe) the output is plain ASCII and no line is cut. `--json` on
`tree`, `show`, `inbox`, `status` and `check` prints the result as JSON.

Exit codes: 0 fine; 1 not complete, or a decision refused; 2 a usage error
(an unknown node too); 3 no Lean.

### Nodes

| Kind | Written as | In Lean |
|---|---|---|
| claim | `Node.claim(id, statement)(formula)`; the one with no parents is the root | proven from its parts (`complete`) |
| invariant | `Node.invariant[A, B](id, statement, why)(rule)`, kept by contracts with `.keeps(inv)(view)` | a claim whose parts are its keepers |
| contract | `Node.contract(op)(id, statement)((a, b, result) => ...)` on an operation `op: Param[(A, B) => R]`, of 0 to 6 inputs | every call of `op` meets `post`; an attached `define` is proven against it (`impl`) |
| contract on a flow | `Node.contract(op)(id, statement)((a, result, before, after) => ...)` on `op: Param[A => Flow[R]]`, of 0 to 6 inputs | every run from any world meets `post`; the attached flow is proven against it on the models (`impl`) |
| assumption | `Node.assumption(op)(...)(post)`, or `Node.assumption(id, statement, why)(formula)` | trusted, not proven: what the outside does, or a fact of the world |
| model of a boundary | `Node.assumption(boundary)(Model)(id, statement, why)` | trusted: the boundary behaves as the model; flows are proven from it |
| definition | `Node.definition(id, statement, why)(Type := of[T], term := expr, ...)` | fixes terms of the vocabulary; decided, not proven |
| design | `Node.design(id, statement, why)(files*)` | none: governs code no proof covers |

A claim or a contract may also give `why = "..."`; without one, the reason it holds is the one the developer
signs with the decision. The other kinds say why.

An operation takes 0 to 6 inputs. Every lambda over a call takes them in order, then the result (a
flow's, then the worlds before and after), and every example lists them the same way. An operation of
no inputs (`Param[() => R]`, a reading of the world now) is called `op()`, its post is `result => ...`
and its examples `expect(result, note)` under the bindings that give it:

```scala
val share = Param[(UserId, DocId, UserId) => Boolean]("share", "whether a user may share a document with another")
Node.contract(share)("Share", "...", why = "...")((by, doc, withWhom, result) => result === owns(by, doc))
  .examples()(expect(ann, readme, bob, true, "the owner shares"), never(bob, readme, ann, true, "only the owner"))
knowledge.implement(share)((by, doc, withWhom) => owners(doc) == by)
```

`.under(parents*)` makes a node a part of each parent. `.replaces(other)` marks
an alternative: accepting one rejects the other. Two definitions of one term
are alternatives too. The root speaks in open terms (`Opaque` types, `Param`
terms); definitions bring in the domain as it is needed.

### Writing formulas and code

Formulas and proven code are written with terms: a `Term[A]` is an expression
of type `A`. It prints as Lean for the proofs and compiles to Scala for the
examples and the checks at run time. What you can write is what the library
offers; anything else is a type error.

```scala
final case class Claims(realm: RealmId, user: String, roles: List[String])
object Claims extends Data[Claims]          // builds Claims from terms: Claims(r, u, rs)

/** The user and roles an answer names, if any. */
val claimsOf = define { (c: Term[Option[Claims]]) =>
  c.fold(none[(String, List[String])])(x => some((x.user, x.roles)))
}
```

| Write | For | In Lean |
|---|---|---|
| `x === y`, `x =!= y` | equality (`==` between terms does not compile) | `=`, `≠` |
| `&&`, `\|\|`, `!`, `==>`, `True`, `False` | logic | `∧`, `∨`, `¬`, `→` |
| `forall((u: Term[User.T]) => ...)`, `exists(...)` | one or two variables; specification only | `∀`, `∃` |
| `s.records`, `CrmStore(a, b, c)`, `a.copy((enabled = v))` | fields, construction, copy (with `object CrmStore extends Data[CrmStore]`) | fields, `CrmStore.mk`, `{ a with ... }` |
| `Event[Event.Expired](now)` | an enum case built from terms (with `object Event extends Data[Event]`) | `Event.Expired now` |
| `q.on[Search.ById](id => ...).on[Search.Everything.type](...)` | a match on an enum (or a list: `.on[::[A]]`, `.on[Nil.type]`), its cases named, in any order; a singleton case is written with `.type` | `match` |
| `c.fold(ifTrue, ifFalse)` | a conditional: Boolean's fold | `if c then a else b` |
| `o.fold(ifEmpty)(x => ...)` | an Option's fold, as Scala's (`ifEmpty` is typed: `List.empty[Rule]`, `none[A]`); `.on` on an Option is refused | `match o with \| some x => ... \| none => ...` |
| `let(v)(x => ...)` | a shared value, named | `let x : A := v; ...` |
| `some(x)`, `none[A]`, `List(a, b)`, `(a, b)`, `t._1` | options, lists and pairs of terms | as Lean's |
| `val d = define { (a: Term[A], b: Term[B]) => ... }` | a named function, in Lean by the val's name | a `def` |

Lambda parameters are annotated (`(s: Term[CrmStore]) => ...`), so the term
knows its type; FrFlow reads the names from the lambda. A `Param` is itself a
term (`grants.contains(g)`, `sessions(t)`). In plain Scala code, call a define
with `d.fn(...)` and read a parameter's value with `p.value`.

On lists: `contains`, `exists`, `forall`, `filter`, `filterNot`, `map`,
`flatMap`, `foldLeft`, `find`, `headOption`, `take`, `drop`, `zip`,
`length`/`size`, `isEmpty`/`nonEmpty`, `::`, `++`, `toSet`. `forall` and
`exists` also take a define of one element (`xs.forall(endsAfterStart)`).
`xs.allDistinct` says no element occurs twice (Lean's `List.Nodup`), and
`xs.pairwise(r)` that `r` holds of every two elements at different positions,
the earlier one first (Lean's `List.Pairwise`; for a symmetric `r`, of every
two); `r` is a define of two elements or a lambda `(a, b) => ...`. On options:
`forall`, `exists`, `contains`, `isDefined`, `isEmpty`, `getOrElse`. On maps:
`get`, `getOrElse`, `contains`, `updated`, `removed`, `+`, `-`. On sets:
`contains`, `+`, `-`, `++`, `intersect`, `subsetOf`. Maps and sets cannot be
iterated. Arithmetic is on `BigInt` (`+`, `-`, `*`, `max`, `min`, comparisons,
`/` and `%` by a literal); `Int` and `Long` compare but do not add.

### Proven, tested, assumed

The code under a contract, or behind a boundary, is in one of three states:

| State | The code | How it is shown to do what is decided |
|---|---|---|
| **proven** | a `define` or a flow, written with terms | Lean proves it meets its contract (`impl`) |
| **tested** | plain Scala: a function, or the project's own implementation of a boundary | FrFlow tests it against its contract, or the boundary's model, on generated cases |
| **assumed** | an outside system behind a boundary (a database), or an assumption on an operation | decided; checked at run time, on the examples and on generated runs |

Lean proves everything above tested and assumed code from the contract or the
model alone (the operation is a parameter, the contract a hypothesis), and
`root_impl` names what it rests on: `trusted: … ; tested, not proven: …`.

**Plain Scala under a contract.** Attach it with `implement`; name the
operations it calls (a call it does not name fails the test):

```scala
.implement(decisionContract)(SessionStore(grants.value.toSet, sessions.value).decide)   // examples/auth
.implement(introspectContract, lookup)(introspection)                                    // examples/keycloak
```

`check` tests it on generated cases (1,000 by default) and on the examples:

- **The property is the contract's formula.** The same term tree Lean reads is
  run in Scala on each case's inputs and the code's result, with the contract's
  `checkedBy` check and the invariants it keeps. No property is written by
  hand.
- **The cases come from the types.** Generators are derived from each type:
  case classes and enums by their fields and cases, lists, options, maps, sets,
  numbers (biased to 0, ±1 and the examples' numbers), opaque terms through the
  definition in force. The world is generated too: the parameters the contract
  reads (`grants`, `sessions`) take generated values, so the code is tested
  over many worlds. The examples' values are seeds, and a third of the cases
  start from an example with one value changed.
- **Coverage is measured on the formula.** Each implication's premise, each
  side of an `||`, each branch and each case of a match must hold in some case.
  A part no case reached is a finding: `its code's tests never reached a part of
  the contract: <part> (add an example, or a generator)`.
- **A failing case is shrunk** (a list loses elements, a number moves toward 0,
  a case class shrinks field by field) and reported at its smallest:
  `its code fails a generated case: ("1a", Path("")) ⇒ Some(UserId("1a")) given
  sessions = {"1a" ↦ Some(UserId("1a")), else None}, grants = List(): …`. It is
  saved in `.frflow/counterexamples.json` (committed) and tried first on every
  later run, until it passes.

`show` prints the result:

```
plain code, tested against the contract, not proven
tested: 1,000 generated cases (seed 1), against DecisionContract
  every case meets it, and every part of it was reached
```

**Generators you give.** Where the derived cases rarely reach a part of the
contract, or where an outside system holds only some values (a table holds
one row per key), give a generator for the type:

```scala
.generating(
  (for rs <- Gen.derived[List[CrmRecord]]; ss <- Gen.derived[List[Share]]; es <- Gen.derived[List[Expiry]]
  yield CrmStore(rs.distinctBy(_.id), ss.distinctBy(s => (s.record, s.to)), es.distinctBy(e => (e.record, e.to))))
    .describedAs("stores with one row per key, as the tables hold them"))   // examples/crm
```

FrFlow says what a given generator makes beside the results, keeps the
examples' values it never makes as seeds, and keeps the derived generator
making a quarter of the type's values, so a narrow generator never hides the
rest. For an outside system's code, a given
generator is all the type is drawn from: data the outside cannot hold is no
finding.

**A service of the project's own** (an in-memory store, a cache) implements a
boundary's trait and is tested against the boundary's state model:

```scala
val tablesModel = Node.assumption(db)(DatabaseModel)("TablesModel", …)
  .checkedAgainst(t => SqliteDatabase.holding(t), _.tables)    // an outside system: assumed, checked
  .implementedBy(t => MemoryDatabase.holding(t), _.tables)     // the project's own code: tested
```

`start` makes an implementation holding a model's state, `read` reads its state
back. FrFlow generates runs (a state, then 1 to 12 calls of the boundary's
operations with generated arguments), runs each on the implementation and on
the model, and compares every result and the state read back after every call.
States are compared as the implementation holds them (stored and read back), so
order it does not keep is not compared. Coverage is of the operations called
and of each branch of the model. A failing run is shrunk to the fewest, smallest
calls: `on LeakyDatabase, from Tables(CrmStore(List(), List(Share(0, TenantId(""))),
List()), List()): storeAbout(0, CrmStore(List(), List(), List()))` with `after
storeAbout(…), LeakyDatabase holds …, where the model holds …`. An outside system
given with `checkedAgainst` goes through the same runs (at most 200), so it is
checked on varied data, not only the examples; its model stays assumed.

**Settings.** `.testedWith(TestSettings(cases = 1000, seed = 1))` on the
knowledge base. `FRFLOW_SEED` replaces the seed for one `check` or `ci`: a
number, or `fresh` for a new one (`FRFLOW_SEED=fresh bin/frflow crm check`). A test's
result is kept while the node's meaning, its code, the settings and the
generators are the same.

**Never weaken a contract to make a test pass.** A failing case is a finding
about the code, or about the contract as decided; changing the contract is a
decision the developer reviews, like any other.

### Decisions

The developer decides every node, once. Whoever writes a node proposes it,
with a `why` and examples; only a decision signed by the developer accepts it. `.frflow/ledger.json` holds each
decision: who, the reason, the alternatives rejected, the commit, a signature,
and the decision before it. The node's content as decided is kept once per
distinct value, so a change adds only what changed.

- **A parent decides its parts.** Adding or removing a part puts the parent up
  for review.
- **Order.** A proposal waits until its parents and the definitions it uses
  are accepted.
- **Mechanical decisions.** A node under review whose own content did not
  change, that Lean proves again (not a definition or design node): one batch,
  `confirm`.
- **Signing.** The developer's key is kept outside the repository
  (`~/.config/frflow/signing.key`, or `FRFLOW_KEY`) and created on the first
  decision; its public key is filed as `.frflow/keys/NAME.pub` and committed.
- **Refused.** A decision on a node that moved since the developer looked at
  it, or with a reason of only a word or two.

A decision binds the reason to the hash of what the developer saw. Whatever
moves under it puts the node back up for review, with the cause:

| Cause | What moved | Shown as |
|---|---|---|
| `self` | what the node says: statement, formula, `why`, examples, terms, kept invariants, implementation source, its section of the idea | a line diff per field |
| `above` | the meaning of a parent, of a definition it uses, or of a contract its code calls | the diff of what moved |
| `parts` | its list of parts | the parts added and removed |
| `code` | the files it governs | a git diff since the decision's commit |
| `revisit` | the developer said a change above may affect it | their reason |
| `merged` | two branches decided it, and the merge kept both | both decisions |

Rewording a `why` or a statement whose formula is unchanged does not cascade
below; a change of formula does. Accepting a change lists every decision that
rests on it, and the developer marks those it may affect (`--revisit`).

### What Lean proves

For each node N with parts C1..Cn, over the open terms they mention, with the
definitions in force applied:

| Obligation | Statement | Fails when |
|---|---|---|
| `complete` | C1 → … → Cn → N | not proven: the parts do not make N (open) |
| `needed_C` (n ≥ 2), tried | N without C | Lean proves it: C is not needed |
| `vacuous` (n = 1), tried | N, with no hypothesis | Lean proves it: N says nothing its part adds |
| `restates` (n = 1), tried | N → C1 | Lean proves it: N says what its part says (a warning) |
| `clash`, tried | C1 → … → Cn → False | Lean proves it: the parts contradict each other |
| `unsat` (every claim), tried | ¬ N | Lean proves it: no world meets N |
| `idle` (the root), tried | the root, with every operation doing nothing (a word marked `.leftOpenAbove` stays open) | Lean proves it: the root does not say what users can do |

`complete` is proven by `frflow_auto` or by hand. The tries use automation
with a small budget, so they catch only what it can show. Then:

- **Composition.** Each node gets `holds`: the leaves below it imply it.
  `root_impl` states the root of the code (each operation with a proven
  `define` replaced by it) from the assumptions alone.
- **Implementations** written as a `define` meet their contract (`impl`),
  proven from the promises of the operations they call, not from their code.
- **Invariants.** A rule over pairs (a reader, a record shown to them). Every
  contract in its scope keeps it (`.keeps`) or says why it is exempt
  (`.exempt`).
- **Examples, both ways.** Lean evaluates each example whose parameters are
  values (or `bindTable` lookups), and probes near them: it must prove what
  Scala computes and not its opposite.
- **State.** A run is `es.foldLeft(init)(step)`; the library (`FrFlow.always`,
  `simulates`, `tracks`) proves properties of every run.
- **Authored proofs** (`lean/Proofs/<KB>/<Node>.lean`) state exactly the
  generated obligation and have their axioms audited (`sorry` fails).

**Checked by running.** Examples run against the contract and the
implementation. In production, `service` binds the operations to their code
and checks results against the contract (or `checkedBy`, a cheaper check
proven to follow from it):

| Code | Checked where it runs, by default | Why |
|---|---|---|
| plain Scala (`implement`), or code beside a proven define (`implementProven(c)(define, runs)`) | every call | its correctness rests on tests |
| an outside system's adapter (an assumption's code) | every call | nothing else guards it |
| a proven define that is the running code (`implementProven(c)(define)`) | not checked | Lean proves its result; checking it again costs a second evaluation of the specification and finds nothing the proof does not |

A different choice is a decision on the node, shown in `show` and in the
summary: `.checkedAtRunTime(RunCheck.Sampled(100))` checks one call in a hundred
(every hundredth, the first included; `Sampled(100, Some(seed))` draws them at
random, reproducibly), `RunCheck.EveryCall` checks every call (for proven code
too), `RunCheck.Never` checks none. Assumptions about the values the code runs
with are checked whatever the choice (once per change of a value they read).

A broken check is reported first, then thrown: the knowledge base's reporter
gets a `Violation` (the contract, which check, the inputs, the result), by
default one line to the platform logger named `frflow`
(`frflow contract violation: contract=Pick check="the contract" inputs=(…) result=…`);
`knowledge.reporting(v => …)` adds your own (a metric, an alert). Then
`ContractViolation` is thrown, so the result is never returned; an application
maps it to its own failure (an HTTP layer, to a 500).

**Effects as assumptions on an operation.** A database or a clock can be an
assumption on an operation; the code is proven from its promise. The adapter
(SQL) is checked against a proven `define` on the examples, on varied data and
on every call. In `examples/crm`, a seeded SQL bug (a dropped `WHERE`) is
stopped this way while every proof still holds. Code that takes several steps
against the outside is written as a flow (next section).

### Effectful code: flows over boundaries

A **boundary** is a trait of operations that take terms and return
flows: what proven code calls but cannot see. Its behaviour is a **state
model**, another implementation of the same trait over a state, which you
decide as an assumption. A **flow** is code over boundaries, written as Cats
code is. Lean proves the flow's contract from the models. From
`examples/crm`:

```scala
trait Database:
  def load: Flow[CrmStore]
  def storeAbout(id: Term[BigInt], t: Term[CrmStore]): Flow[Unit]
  def logEvent(e: Term[Event]): Flow[Unit]

val db = Boundary[Database]("database", "the SQLite database the CRM keeps its records, shares, expiries and event log in")

object DatabaseModel extends Database, StateModel[Tables]:
  def load = state.get.map(t => t.store)
  def storeAbout(id: Term[BigInt], s: Term[CrmStore]) = state.update(t => Tables(replaceAbout(t.store, id, aboutRecord(s, id)), t.events))
  def logEvent(e: Term[Event]) = state.update(t => Tables(t.store, t.events ++ List(e)))

def expireOnce(now: Term[BigInt]): Flow[CrmStore] =
  for
    s <- db.load
    t  = expire(s, now)
    _ <- changedIds(s, t).traverse_(id => db.storeAbout(id, t))
    _ <- db.logEvent(Event[Event.Expired](now))
  yield t
```

A flow is a monad relative to `Term` (`RelativeMonad[Flow, Term]`): `pure` and
`flatMap` take terms rather than values, so a flow can be printed as Lean as
well as run. It is a free one: the laws (left unit, right unit,
associativity) hold of what a flow gives in Lean's `do` and at run time, not
of its tree; FrFlow's own suites test them on both. Its combinators are
Cats', with Cats' names:

| Write | For | In Lean |
|---|---|---|
| `for x <- f yield t`, `f.flatMap(x => g)`, `f.map(x => t)`, `Flow.pure(t)` | steps in order | `let x ← f`, `pure t` |
| `f *> g`, `f <* g`, `f.as(t)`, `f.void`, `f.flatTap(x => g)`, `f.product(g)`, `(f, g).tupled` | steps whose result is kept or dropped | `do` steps |
| `c.foldF(f, g)`, `Flow.whenA(c)(f)`, `Flow.unlessA(c)(f)`, `Flow.ifM(fc)(f, g)` | a branch on a term, on a term only when it holds or not, on a flow's result | `if c then ... else ...` |
| `xs.traverse_(x => f)`, `xs.traverse(x => f)`, `xs.foldM(z)((acc, x) => f)`, `Flow.sequence(fs)` | each element in turn: nothing kept, the results, an accumulator, a list of flows | `for x in xs do`, `xs.mapM`, `xs.foldlM`, a `let` per flow |

- **The model** is decided with `Node.assumption(db)(DatabaseModel)(id,
  statement, why)`. It reads and changes its state with `state.get`,
  `state.set(s)` and `state.update(f)`. A state model assumes the boundary is
  deterministic (what is unknown, such as a clock's readings, goes into the
  state), never fails on its own (a boundary that may fail is declared so: see
  "Failures" below), and is the flow's alone during a run; loops are over
  lists (`xs.traverse_(x => ...)`, `xs.traverse`, `xs.foldM`). A design node says how the exclusive
  access is ensured (in the CRM, a lock).
- **The contract** is on an operation `Param[A => Flow[R]]` (of 0 to 6 inputs:
  `() => Flow[R]`, `(A, B) => Flow[R]`); its post relates the inputs, the result
  and the states before and after:
  `(now, result, before, after) => sameRows(after(DatabaseModel).store, expire(before(DatabaseModel).store, now)) && ...`.
  Its examples give the inputs, a world before (`World(DatabaseModel -> Tables(...))`)
  and the result and world after: `expect(now, before, result, after, note)`.
- **The code** is attached with `.implementProven(expiryJob)(expireOnce)`. In
  Lean it is a `do` block over any monad with the boundaries' classes, and
  `impl` runs it on the models (`StateM World`). Steps of the outside world
  (`Flow.effect`) belong to production implementations only; a proven flow
  takes none.
- **Production** binds an implementation of the trait, its operations built
  with `Flow.effect`, and runs the flow in any `cats.effect.Sync`:
  `knowledge.run[SyncIO](expiryJob)(db.bind(SqliteDatabase(d)))(now)`.
- **Implementations against the model.** `.checkedAgainst(start, read)` on the
  model's node names an outside system (SQLite): its model stays assumed, and
  it is checked against the model on the contract's examples and on generated
  runs of its operations. `.implementedBy(start, read)` names the project's own
  implementation (the CRM's `MemoryDatabase`): it is tested against the model
  on generated runs, as described under "Proven, tested, assumed".

### Time: the clock, sleeping, deadlines

Time is a boundary like any other: `Clock` (`now`, `sleep`) with its model
`ClockModel`, whose state `ClockState(now, delays)` holds the time and the delays
still to come. Steps take no time (the synchronous hypothesis): time passes at a
sleep and between the system's events. A sleep of `d` wakes `d` seconds later plus
the next delay, never earlier, so a flow is proven for every start time and every
late wake-up. Decide the model with `Node.assumption(Clock.boundary)(ClockModel)(…)`
and test a fake clock against it (`.implementedBy(c => FakeClock(c), _.state)`);
the computer's clock (`SystemClock`) stays assumed.

| Write | For | In Lean |
|---|---|---|
| `Flow.now`, `Flow.sleep(d)` | the time; waiting | `Clock.now`, `Clock.sleep d` |
| `Flow.waitUntil(t)` | waiting until a time (no sleep when it is past) | `if now < t then Clock.sleep (t - now)` |
| `f.timeout(d)` | `Some(result)` when `f` took at most `d`, `None` otherwise; no cancellation, `f`'s changes stay | two readings around `f` |
| `Flow.every(period)(job)` | a periodic job: `.once`, `.runs(ticks)` (a `for` loop for proofs), `.schedule[G](clock, times, started)(run)` (the scheduler) | `for _ in ticks do job; Clock.sleep period` |

Where time enters the tree is a choice: keep the root timeless, with the words
that depend on time (a share *in force*, an invitation *open*) as operations the
upper nodes leave open, and fix them with the clock lower down, in their contracts,
marked `.leftOpenAbove`: a statement that names such an operation holds whatever it
does, so a change to that contract (7 days become 14) does not bring it back. Claims over runs (deadlines:
"within 30 days and the scheduler's period") are stated of the state after a list of
events (`events.foldLeft(start)(step)`), with the scheduler's period and "the clock
never goes back" as assumptions on the run (`events === pre ++ (e :: post) ==> …`),
and proven by induction over the run (`FrFlow.always_when`, `FrFlow.along_when`).
Put each deadline under the branch whose proof uses it: the branch says it with the
open word ("no invitation is pending a housekeeping period after it lapses"), the
deadline with the clock ("7 days and two minutes"), and the timed contract links the
two. The `idle` try keeps such words open, so the root need not list what they must
at least allow to keep "doing nothing" from meeting it.
`examples/sharing` does all of this (`time/`, `housekeeping/`).

### Failures: errors, retries, what a failed run leaves

A boundary that may fail is declared with its error:
`Boundary.failing[LibraryStore]("store", "...")(Failure.StoreUnavailable)`. Any call
of it may then fail with that error, changing nothing of its model. In the proofs,
the world holds the faults (`faults : List Bool`): each call of a failing boundary
takes the next, and `true` fails it; a flow is proven for every pattern of faults,
so for a store that fails at any step. A flow that may fail runs in Lean's
`ExceptT E (StateM World)`: a step that fails changes nothing, the steps before it
stay done (the clock moved, a mail sent), and the run gives its outcome and the
world after (`FrFlow.runOnE`). "A failed request changes nothing" is then a claim
of the flow, proven, not an axiom of the semantics: true of a flow whose only
change is one save, false of one that saves twice. In production an exception from a
failing boundary's implementation is its error.

| Write | For | In Lean |
|---|---|---|
| `Flow.raiseError[A](e)` | failing with `e` (MonadError's `raiseError`) | `throwThe E e` |
| `f.handleErrorWith[E](e => g)` | `g` on an error of type `E` | `tryCatchThe E (do f) (fun e => do g)` |
| `f.attempt[E]` | the outcome: `Left(error)` or `Right(result)`, never failing; `o.fold(e => …, r => …)` | `tryCatchThe` to an `Except E R` |
| `f.retry[E](Schedule.exponential(1, retries = 2))` | `f` tried again after each wait of the schedule (a value: `Schedule(waits)`, `fixed`, `exponential`) | one `tryCatchThe` inside the other, a `Clock.sleep` before each |
| `f.guarantee[E](fin)`, `Flow.bracket[E](acquire)(use)(release)` | `fin` (`release`) after `f` (`use`) whether it gave a result or failed; the error raised again | a handler that runs `fin` and throws again, `fin` after the result |

A contract on a flow that may fail says what holds when a run fails:
`.failsChangingNothing[E]` (every model's state after it is as before), or
`.onFailure[E]((error, before, after) => …)`; its post is what holds of a run that
succeeds. Lean's claim is `FrFlow.outcome post failure (op x w)` of every input and
every world. A flow that may fail under a contract that says nothing of failing is a
problem `check` reports. The examples give a run that fails as `Failed(error)`,
from a world that fails some calls: `expect(r, before.failing(false, true),
Failed(Failure.StoreUnavailable), before, "the store fails as it saves")`.
Generated runs then fail each call of a failing boundary in turn, from each example,
on the models and on the implementations with the same fault injected (`FaultPlan`),
and check the failure clause; `frflow_auto` takes each case of the faults
(`frflow_faults`). `examples/sharing` does this (`store/`, `notifications/`,
`http/SharingHttp.scala`).

### Concurrency: branches at once, races, transactions

Flows can run branches at once, with Cats Effect's names; all are structured (no
branch outlives the flow that started it; a cancelled branch runs its finalizers).

| Write | For | In Lean | At run time (IO) |
|---|---|---|---|
| `(fa, fb).parTupled` | both at once, results paired | `fa` then `fb` (`tupled`), and `commute_i`: the two orders give the same | `IO.both` on fibers |
| `xs.parTraverse(f)`, `xs.parTraverseN(4)(f)` | each element at once (at most 4) | `xs.mapM f`, and `commute_i`: any two elements commute | `parTraverseN` |
| `f.race(g)` | the first to finish; the other cancelled | the scheduler's choice (`Races` boundary, a model whose state is the outcomes, so a claim holds for either); a losing transaction left nothing or all of itself | `IO.race` |
| `Flow.atomically(f)` | one step of the world: a transaction | `f` (one event of a run) | a lock on each boundary `f` calls, taken in one order; once begun, not cancelled |
| `f.guarantee[E](fin)` | as before, and `fin` when `f` is cancelled | as before | `onCancel` |

What is proven, and what is not:
- **Whole branches commute.** For each `parTupled` and `parTraverse` of proven code,
  the obligation `commute_i` says the two orders of whole branches give the same
  result and world, for every world with no call failing (the faults are taken in
  the order calls come, so which call fails depends on the order). `frflow_auto`
  closes it for branches on different models or whose changes commute
  (`FrFlow.Commute` and its lemmas in `lean/FrFlow/Commute.lean`); otherwise it is
  proven by hand. A node with a branch not proven to commute is open, not proven.
  Pairwise commutation of a traverse's elements gives every order of whole branches
  (by swapping neighbours, `Commute.swap`); that step is not mechanized.
- **Interleavings are tested, not proven.** Two branches' steps can interleave. Where
  branches share a model, the shared read-and-write goes in `atomically`; the
  generated tests then run each example's flow on the implementations in IO, eight
  times, with a random pause before each call, and compare with the models' run in
  turn. A flow that reads and writes shared state outside a transaction is caught
  there (a lost update), not by `commute_i`.
- **A transaction is one step by decision.** Lean reads `atomically` as its body: a
  run of requests proven event by event is a proof of their serial orders. That the
  runtime gives it is FrFlow's lock (one process) and, in a project, a decided node
  (`examples/sharing`: `Transactions`). More than one process needs the store to
  give it (compare-and-set, or the database's transactions).
- **Proven branches may not fail**: each handles its errors (`attempt`,
  `handleErrorWith`), so one branch failing never cancels the other halfway; no
  transaction or branch inside a transaction; a race in proven code is between a
  timer (a flow of the clock only) and one transaction, or two timers.
- In `SyncIO` (and on the models) branches run in turn: the reading the proofs make.
  On the computer's clock in IO a sleep blocks no thread and is cancelled with its
  fiber.

A flow over a `parTraverse` is proven with `FrFlow.outcome_mapM_void` (each branch
keeps an invariant from any state it holds of, and never fails). `examples/sharing`
delivers four notices at once (`notifications/`, `DeliveryJob`), runs each request
and housekeeping as a transaction, and tests many clients at once against the log's
commit order (`SharingSuite`).

### What is trusted, and the limits

Lean proves the nodes consistent with each other and the root of the code;
the developer decides that they are the right theory. Trusted:

- the assumptions (the hypotheses of `root_impl`), checked where they can be;
- the printing of terms as Lean and their evaluation as Scala, cross-checked
  on the examples and on probes near them; the library offers no operation it
  cannot print faithfully (`Int` arithmetic is a type error);
- tested code: plain Scala under a contract, and the project's own
  implementations of a boundary, tested on generated cases, not proven: the
  tests show the code meets its contract or model on the cases they reached,
  and say which parts of it they never reached;
- the state models of boundaries: that an outside system behaves as its model,
  checked on the examples and on generated runs where `.checkedAgainst` is given;
- that parameters hold the data they are said to mean, and that every path to
  the data goes through `service`: design nodes are reviewed, not proven;
- the signing key, kept outside the repository the agent edits;
- the model's program. FrFlow runs it to read it, so the gate stops drift, not
  an agent that writes code to subvert FrFlow.

Limits: the tries are one-sided. Examples with function-valued parameters
(other than `bindTable`) are not evaluated in Lean. Testing covers the examples
and the generated cases, not every input. Liveness is not covered. Interleavings of
concurrent branches are tested, not proven (see [Concurrency](#concurrency-branches-at-once-races-transactions)).
Maps and sets cannot be iterated.

### Warnings

`status` exits 1 unless every node is accepted, nothing is left unproven, no
node is gone, and there is no warning. The warnings:

- no developer key, or a decision not signed by a filed key;
- a source file governed by two nodes or by none, or a governed file that
  does not exist;
- a section of `IDEA.md` no node names, or one a node names that the idea
  lacks;
- a proof file of no node;
- a contract none of whose examples Lean evaluates;
- a node that only restates its part.

### CI

Committed: the Scala, `IDEA.md`, `.frflow/` (the ledger and keys; with the agent layer, its requests and conversation) and
`lean/Proofs`; the rest is derived. CI runs `ci`, caching
`.frflow/checks.json` and `lean/.lake` by branch, so only what changed is
proven again. The repository has no CI configuration of its own; a CI job runs
the tests twice, with the fixed seed and with a fresh one, so that a case the
fixed seed never makes can still be found (a failing case is kept in
`.frflow/counterexamples.json`, to commit):

```
bin/frflow crm ci
FRFLOW_SEED=fresh bin/frflow crm ci
```

FrFlow's own suites (`sbt testAll`) keep the seeds they set, so their results do
not depend on the environment.

### A new project

`sbt "frflowInit library"` makes `examples/library` with an empty knowledge base and its command line, and adds
`lazy val library = example("library", layers = Nil)` to `build.sbt` (add it to `root`'s `aggregate` to test it with the rest);
then `sbt reload`. The rest follows [Starting a project](#starting-a-project). `bin/frflow library render` creates
`lean/` (its `lakefile.toml`, toolchain and the generated Lean) once there are nodes; with several mains in the
project, set `Compile / run / mainClass`.

### Web view

`sbt "PROJECT/serve [--port N] [--as NAME]"` serves the developer's flow
in a browser, from the project's main object in a JVM of its own: the DAG with each node's state and status, a node with its diff
since it was decided, the inbox, and the decisions with their reasons. It listens on localhost (port 8765 by
default) and prints a link with a random token, which every route asks for. `IDEA.md` waits there too, first.
A layer on top adds its routes, behind the same token, and its script (`/ext.js`), which hooks into the page
(`FrFlow.extend`).

The page is a client of the same API as the CLI (`FrFlowApi`), so a decision is
signed and recorded as `accept` records it, and the CLI can run beside it. The
server runs the model it compiled when it started: once the model's sources
change, the page says so and refuses decisions until it is restarted.

### Modules

One sbt subproject each, under `modules/`:

- `protocol` (package `frflow.protocol`): the data crossing modules and files,
  with JSON codecs: ids, statuses and contents; the developer's decisions
  (`decision`), what checks record (`obligation`), the snapshot (`snapshot`).
- `model` (package `frflow`): nodes and knowledge bases; `Opaque`, `Param`,
  `define`; terms, their Lean and their evaluation; flows, boundaries and
  state models; examples, probes, `service`, `run`. A package per concept
  (`term`, `types`, `vocabulary`, `node`, `kb`, `flow`, `boundary`, `runtime`,
  `example`, `testing`, `program`); the trees and steps a model is made into,
  their Lean and their Scala, are in `frflow` itself. A model needs only
  `import frflow.*`.
- `lean` (package `frflow.lean`): the Lean of a knowledge base; `printing`, its
  modules and proof files; `obligation`, what Lean is asked of each node and the
  examples it evaluates; `reading`, reading Lean's output and proof files.
- `ledger` (package `frflow.ledger`): decisions and refusals; `review`, review
  states and decision rules; `report`, reports; `signing`, keys and signatures;
  `store`, the files.
- `check` (package `frflow.check`): the workspace and what the checker reads;
  `analysis`, the contents, the hashes and the snapshot; `proving`, render,
  check and scaffold; `process`, running `lake` and git.
- `api`: `FrFlowApi`, the operations a front end calls; a node's details and diff in `frflow.api.details`, what
  the reads and operations return in `frflow.api.report` (both re-exported from `frflow.api`).
- `cli`: the command line over the API; the commands and their dispatch in `frflow.cli.command`, the views as text in
  `frflow.cli.text`.
- `web`: the web view over the API. The CLI does not depend on it.
- `agent` (package `frflow.agent`): the AI agent's layer, on top of `cli` and `web`. No other module depends on it.
  Its sub-packages: `conversation`, `request`, `queue` (what is the agent's to do), `command` (its commands and their
  text) and `panel` (its routes in the web view).

`lean`, `ledger` and `check` re-export the names of their sub-packages (each
`package.scala`), so `import frflow.ledger.*` reaches `Decide` and `JsonStore` alike.

The Lean library is in `lean/FrFlow/`.

### Measurements

`python3 bench/generate.py N` writes `examples/scale`, a synthetic project:
one root over N services grouped five by five, each service a claim with two
or three parts and a contract with proven code. `bench/measure.sh 20 60`
times a cold check, then one change of each kind. On a 4-core container
with nothing else running:

| nodes | cold `check` | one code change | one claim change | one definition change | `status` |
|---|---|---|---|---|---|
| 103 | 92 s | 14 s | 15 s | 45 s | 2.2 s |
| 305 | 234 s | 19 s | 21 s | 125 s | 4.3 s |

The code change is one service's code; the claim change strengthens one
service's part; the definition change is a limit about a third of the nodes
use. After a cold check, only what a change reaches is proven again.

## With an AI agent

The agent layer (`modules/agent`, package `frflow.agent`) adds what an agent working in the project needs: its
commands, the developer's requests to it, the conversation the idea comes from, and their parts of `inbox`, `show`,
`review`, `status` and the web view. It keeps its own files, `.frflow/requests.json` and
`.frflow/conversation.json`; the core does not read them. The agent's rules are in
[`.claude/skills/frflow/SKILL.md`](../.claude/skills/frflow/SKILL.md).

### Enabling it

A project enables it on its main object, and depends on the module in `build.sbt` (`example(NAME)` does, by
default; `example(NAME, layers = Nil)` does not):

```scala
object authCli extends frflow.cli.FrFlowApp(knowledge, root = "examples/auth", extensions = List(frflow.agent.Agent))
```

`sbt "frflowInitAgent NAME"` sets up a new project this way. The layer is an `Extension` of the core's: a
`CliExtension` (its commands, and what it adds to a view) and a `WebExtension` (its routes and script); another
layer is written the same way.

### Its commands

| | command | what it does |
|---|---|---|
| developer | `ask NODE TEXT`, `ask --idea TEXT`, `close REQUEST...` | ask the agent for a change; close an answer read |
| | `conversation` | what you told the agent, its questions with the answers it assumed, and yours |
| | `review` | also offers `[?]ask`: ask the agent for a change instead of deciding |
| agent | `said TEXT`, `asked QUESTION --assume ANSWER`, `replied Q TEXT` | record the conversation the idea comes from |
| | `context NODE` | everything on a node (`show --full`), its requests, and the agent's rules |
| | `answer REQUEST\|NODE TEXT` | reply to a request, or tell the developer of work they did not ask for |

A node asked of the agent waits with the agent, not in the developer's queue, until it answers or the node changes.
A rejected node, and a revisit, are listed for the agent in `inbox`.

### Starting a project with the agent

1. `sbt "frflowInitAgent NAME"` sets up an empty project with the agent layer.
2. The developer tells the agent the idea in chat. The agent asks what it needs, three to five questions at a time,
   each with the answer it assumes, and records the conversation as it goes: `said` (the developer's words, verbatim),
   `asked` (a question and the assumed answer, numbered `Q1`, `Q2`, ...) and `replied` (the developer's answer, as
   said in chat). This is a record, kept in `.frflow/conversation.json`, not a decision: the agent cannot sign as the
   developer. `conversation` shows it; `inbox` and `status` list the questions with no reply yet.
3. The agent writes `IDEA.md` from the conversation. Each section names the answers it comes from on a `From:` line
   (`From: Q1, Q3`), which moves no node.
4. `IDEA.md` waits for the developer, who accepts it or asks the agent to change it (`ask --idea TEXT`).
5. The agent proposes the root, then its parts, each naming the section of `IDEA.md` it comes from.

A change to a section's `From:` lines brings back only `IDEA.md`. A changed answer to a question is a warning in
`status` until `IDEA.md` is looked at and accepted again; so is a section naming a question the conversation does
not have.

### In the web view

With the layer, the page lists the agent's open questions (answered in chat) and the requests, offers to ask the
agent for a change on a node and on `IDEA.md`, and shows the nodes with the agent. Agents use the CLI, not the web
view.
