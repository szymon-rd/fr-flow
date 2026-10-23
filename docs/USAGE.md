# Using FrFlow

The reference for the CLI and what it checks. The [README](../README.md)
explains the idea; [DAG.md](DAG.md) is the design.

## Running

Requirements: JDK 17+, sbt, and Lean 4.35.0 (`lake` on the `PATH`, or
`FRFLOW_LAKE`). `bin/frflow PROJECT COMMAND` runs a project's CLI
(`bin/frflow auth tree`), compiling with sbt on first use and after a change.
`--help` lists the commands.

Tests: `sbt test` runs the fast ones (about a minute). The tests that run Lean end to end (tagged `Lean`, several
minutes) run with `sbt leanTest`; `sbt testAll` runs both, as before a merge.

## Commands

| | command | what it does |
|---|---|---|
| developer | `tree [NODE]` | the DAG from the root (or below NODE): status, kind and state, statement |
| | `show NODE`, `diff NODE` | a node in about a screen; what changed since it was decided |
| | `inbox` | what waits for whom, then the summary |
| | `review` | decide what waits, parents first: `[a]ccept [r]eject [s]kip [v]iew [q]uit [?]ask` |
| | `accept NODE...`, `reject NODE`, `confirm`, `revisit NODE`, `gone NODE` | one decision, with `-m REASON`; confirmed on a terminal, `--yes` without one |
| | `ask NODE TEXT`, `ask --idea TEXT`, `close REQUEST...` | ask the agent for a change; close an answer read |
| | `conversation` | what you told the agent, its questions with the answers it assumed, and yours |
| agent | `said TEXT`, `asked QUESTION --assume ANSWER`, `replied Q TEXT` | record the conversation the idea comes from (see [Starting a project](#starting-a-project)) |
| | `inbox`, `context NODE`, `find WORDS\|PATH` | what to do; everything on a node (`show --full`); where a change belongs |
| | `render`, `check [NODE]`, `scaffold NODE` | Lean and `.frflow/kb.json`; prove what changed; proof stubs for what is left open |
| | `status`, `ci` | the tree, the summary and the warnings; exit 1 unless complete (`ci` checks first) |
| | `answer REQUEST\|NODE TEXT` | reply to a request, or tell the developer of work they did not ask for |

`--as NAME` names who decides (default: `FRFLOW_AS`, or the name the key is
filed under). The commands that decide, and the web view, ask for it when neither is
set.

`accept IDEA` accepts `IDEA.md` (see below); `IDEA` is not a node id.

The web view is not a command: it is an sbt task, `sbt "PROJECT/serve [--port N] [--as NAME]"`
(see [Web view](#web-view)).

## Starting a project

1. `sbt "frflowInit NAME"` sets up an empty project in `examples/NAME`: a knowledge base with no nodes, its main
   object, its Lean project, and its line in `build.sbt` (then `sbt reload`).
2. The developer tells the agent the idea in chat. The agent asks what it needs, three to five questions at a time,
   each with the answer it assumes, and records the conversation as it goes: `said` (the developer's words, verbatim),
   `asked` (a question and the assumed answer, numbered `Q1`, `Q2`, ...) and `replied` (the developer's answer, as
   said in chat). This is a record, kept in `.frflow/conversation.json`, not a decision: the agent cannot sign as the
   developer. `conversation` shows it; `inbox` and `status` list the questions with no reply yet.
3. The agent writes `IDEA.md` from the conversation. Each section names the answers it comes from on a `From:` line
   (`From: Q1, Q3`), which moves no node.
4. `IDEA.md` waits for the developer, first in `inbox` and `review`: they accept it (`accept IDEA`, signed, or in the
   web view) or tell the agent what to change. The root is decided after it.
5. The agent proposes the root, then its parts, each naming the section of `IDEA.md` it comes from (`idea = "..."`).

Later, a change to `IDEA.md` brings it back for review, and the root waits for it again. A change to what a section
says brings back the nodes that name that section; a change to its `From:` lines brings back only `IDEA.md`. A
changed answer to a question is a warning in `status` until `IDEA.md` is looked at and accepted again.

## Output and exit codes

On a terminal the output has colors and Unicode and fits the terminal's width:
formulas, diffs and decisions wrap, other lines are cut (`context` shows them
whole). `--plain`, `NO_COLOR` or `TERM=dumb` turn this off. Off a terminal (CI,
agents, a pipe) the output is plain ASCII and no line is cut. `--json` on
`tree`, `show`, `inbox`, `status` and `check` prints the typed value.

Exit codes: 0 fine; 1 not complete, or a decision refused; 2 a usage error
(an unknown node too); 3 no Lean.

## Nodes

| Kind | Written as | In Lean |
|---|---|---|
| claim | `Node.claim(id, statement, why)(formula)`; the one with no parents is the root | proven from its parts (`complete`) |
| invariant | `Node.invariant[A, B](id, statement, why)(rule)`, kept by contracts with `.keeps(inv)(view)` | a claim whose parts are its keepers |
| contract | `Node.contract(op)(id, statement, why)(post)` on an operation `op: Param[(A, B) => R]` | every call of `op` meets `post`; an attached `define` is proven against it (`impl`) |
| contract on a flow | `Node.contract(op)(id, statement, why)((a, result, before, after) => ...)` on `op: Param[A => Flow[R]]` | every run from any world meets `post`; the attached flow is proven against it on the models (`impl`) |
| assumption | `Node.assumption(op)(...)(post)`, or `Node.assumption(id, statement, why)(formula)` | trusted, not proven: what the outside does, or a fact of the world |
| model of a boundary | `Node.assumption(boundary)(Model)(id, statement, why)` | trusted: the boundary behaves as the model; flows are proven from it |
| definition | `Node.definition(id, statement, why)(Type := of[T], term := expr, ...)` | fixes terms of the vocabulary; decided, not proven |
| design | `Node.design(id, statement, why)(files*)` | none: governs code no proof covers |

`.under(parents*)` makes a node a part of each parent. `.replaces(other)` marks
an alternative: accepting one rejects the other. Two definitions of one term
are alternatives too. The root speaks in open terms (`Opaque` types, `Param`
terms); definitions bring in the domain as it is needed.

## Writing formulas and code

Formulas and proven code are written with terms: a `Term[A]` is a value of
type `A` as FrFlow sees it. It prints as Lean for the proofs and compiles to
Scala for the examples and the checks at run time. There is no macro: what you
can write is what the library offers, and anything else is a type error.

```scala
final case class Grant(user: UserId, path: Path)
object Grant extends Data[Grant]          // builds a Grant from terms: Grant(u, p)

/** The decision as Lean proves it meets the contract: the reference the running code is checked against. */
val admitted = define { (token: Term[String], path: Term[Path]) =>
  sessions(token)
    .on[Some[UserId]](u => If(grants.contains(Grant(u, path)))(some(u)).Else(none))
    .on[None.type](none)
}
```

| Write | For | In Lean |
|---|---|---|
| `x === y`, `x =!= y` | equality (`==` between terms does not compile) | `=`, `≠` |
| `&&`, `\|\|`, `!`, `==>`, `True`, `False` | logic | `∧`, `∨`, `¬`, `→` |
| `forall((u: Term[User.T]) => ...)`, `exists(...)` | one or two variables; specification only | `∀`, `∃` |
| `s.records`, `CrmStore(a, b, c)`, `a.copy((enabled = v))` | fields, construction, copy (with `object CrmStore extends Data[CrmStore]`) | fields, `CrmStore.mk`, `{ a with ... }` |
| `Event[Event.Expired](now)` | an enum case built from terms (with `object Event extends Data[Event]`) | `Event.Expired now` |
| `q.on[Search.ById](id => ...).on[Search.Everything.type](...)` | a match; a singleton case is written with `.type`; Options and lists alike (`.on[Some[A]]`, `.on[None.type]`) | `match` |
| `If(c)(a).Else(b)` | a conditional | `if c then a else b` |
| `let(v)(x => ...)` | a shared value, named | `let x : A := v; ...` |
| `some(x)`, `none[A]`, `List(a, b)`, `(a, b)`, `t._1` | options, lists and pairs of terms | as Lean's |
| `val d = define { (a: Term[A], b: Term[B]) => ... }` | a named function, in Lean by the val's name | a `def` |

Lambda parameters are annotated (`(s: Term[CrmStore]) => ...`), so the term
knows its type; FrFlow reads the names from the lambda. A `Param` is itself a
term (`grants.contains(g)`, `sessions(t)`). In plain Scala code, call a define
with `d.fn(...)` and read a parameter's value with `p.value`.

On lists: `contains`, `exists`, `forall`, `filter`, `filterNot`, `map`,
`flatMap`, `foldLeft`, `find`, `headOption`, `take`, `drop`, `zip`,
`length`/`size`, `isEmpty`/`nonEmpty`, `::`, `++`, `toSet`. On options:
`forall`, `exists`, `contains`, `isDefined`, `isEmpty`, `getOrElse`. On maps:
`get`, `getOrElse`, `contains`, `updated`, `removed`, `+`, `-`. On sets:
`contains`, `+`, `-`, `++`, `intersect`, `subsetOf`. Maps and sets cannot be
iterated. Arithmetic is on `BigInt` (`+`, `-`, `*`, `max`, `min`, comparisons,
`/` and `%` by a literal); `Int` and `Long` compare but do not add.

## Decisions

The developer decides every node, once. The agent proposes, with a `why` and
examples; no command of the agent's decides. `.frflow/ledger.json` holds each
decision: who, the reason, the alternatives rejected, the commit, a signature,
and the decision before it.

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

## What Lean proves

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
| `idle` (the root), tried | the root, with every operation doing nothing | Lean proves it: the root does not say what users can do |

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
and checks every result against the contract (or `checkedBy`, a cheaper check
proven to follow from it), raising `ContractViolation`.

**Effects as assumptions on an operation.** A database or a clock can be an
assumption on an operation; the code is proven from its promise. The adapter
(SQL) is checked against a proven `define` on the examples, on varied data and
on every call. In `examples/crm`, a seeded SQL bug (a dropped `WHERE`) is
stopped this way while every proof still holds. Code that takes several steps
against the outside is written as a flow (next section).

## Effectful code: flows over boundaries

A **boundary** is a plain trait of operations that take terms and return
flows: what proven code calls but cannot see. Its behaviour is a **state
model**, another implementation of the same trait over a state, which you
decide as an assumption. A **flow** is code over boundaries, written as Cats or
ZIO code is. Lean proves the flow's contract from the models. From
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

- **The model** is decided with `Node.assumption(db)(DatabaseModel)(id,
  statement, why)`. It reads and changes its state with `state.get`,
  `state.set(s)` and `state.update(f)`. A state model assumes the boundary is
  deterministic (what is unknown, such as a clock's readings, goes into the
  state), never fails, and is the flow's alone during a run; loops are over
  lists (`xs.traverse_(x => ...)`). A design node says how the exclusive
  access is ensured (in the CRM, a lock).
- **The contract** is on an operation `Param[A => Flow[R]]`; its post relates
  the input, the result and the states before and after:
  `(now, result, before, after) => sameRows(after(DatabaseModel).store, expire(before(DatabaseModel).store, now)) && ...`.
  Its examples give a world before (`World(DatabaseModel -> Tables(...))`)
  and the result and world after.
- **The code** is attached with `.implementProven(expiryJob)(expireOnce)`. In
  Lean it is a `do` block over any monad with the boundaries' classes, and
  `impl` runs it on the models (`StateM World`). Steps of the outside world
  (`Flow.effect`) belong to production implementations only; a proven flow
  takes none.
- **Production** binds an implementation of the trait, its operations built
  with `Flow.effect`, and runs the flow in any `cats.effect.Sync`:
  `knowledge.run[SyncIO](expiryJob)(db.bind(SqliteDatabase(d)))(now)`.
  `.checkedAgainst(start, read)` on the model's node checks the production
  implementation against the model on the contract's examples: both start
  from the same state, and must end with the same result and state.

## What is trusted, and the limits

Lean proves the nodes consistent with each other and the root of the code;
the developer decides that they are the right theory. Trusted:

- the assumptions (the hypotheses of `root_impl`), checked where they can be;
- the printing of terms as Lean and their evaluation as Scala, cross-checked
  on the examples and on probes near them; the library offers no operation it
  cannot print faithfully (`Int` arithmetic is a type error);
- the state models of boundaries: that the production implementation behaves
  as its model, checked on the examples where `.checkedAgainst` is given;
- that parameters hold the data they are said to mean, and that every path to
  the data goes through `service`: design nodes are reviewed, not proven;
- the signing key, kept outside the repository the agent edits;
- the model's program. FrFlow runs it to read it, so the gate stops drift, not
  an agent that writes code to subvert FrFlow.

Limits: the tries are one-sided. Examples with function-valued parameters
(other than `bindTable`) are not evaluated in Lean. Running covers the
examples and their combinations, not every input. Ordering, liveness, failures
of the outside world, and concurrent access to a boundary are not covered. Maps and sets
cannot be iterated.

## Warnings

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

## CI

Committed: the Scala, `IDEA.md`, `.frflow/` (ledger, keys, requests, the conversation) and
`lean/Proofs`; the rest is derived. CI runs `ci`, caching
`.frflow/checks.json` and `lean/.lake` by branch, so only what changed is
proven again.

## A new project

`sbt "frflowInit library"` makes `examples/library` with an empty knowledge base and its command line, and adds
`lazy val library = example("library")` to `build.sbt` (add it to `root`'s `aggregate` to test it with the rest);
then `sbt reload`. The rest follows [Starting a project](#starting-a-project). `bin/frflow library render` creates
`lean/` (its `lakefile.toml`, toolchain and the generated Lean) once there are nodes; with several mains in the
project, set `Compile / run / mainClass`.

## Web view

`sbt "PROJECT/serve [--port N] [--as NAME]"` serves the developer's flow
in a browser, from the project's main object in a JVM of its own: the DAG with each node's state and status, a node with its diff
since it was decided, the inbox, the decisions with their reasons, and
requests to the agent. It listens on localhost (port 8765 by default) and
prints a link with a random token, which every route asks for. `IDEA.md` waits there too, first, and the agent's
open questions are listed (they are answered in chat).

The page is a client of the same API as the CLI (`FrFlowApi`), so a decision is
signed and recorded as `accept` records it, and the CLI can run beside it. The
server runs the model it compiled when it started: once the model's sources
change, the page says so and refuses decisions until it is restarted. Agents
use the CLI, not the web view.

## Modules

One sbt subproject each, under `modules/`:

- `protocol`: the data crossing modules and files, with JSON codecs.
- `model` (package `frflow`): nodes and knowledge bases; `Opaque`, `Param`,
  `define`; terms, their Lean and their evaluation; flows, boundaries and
  state models; examples, probes, `service`, `run`.
- `lean`: the Lean of a knowledge base, and reading Lean's output.
- `ledger`: review states and decision rules; reports; stores, keys and
  signatures.
- `check`: render and check (running `lake`), the snapshot, status, scaffold,
  git.
- `api`: `FrFlowApi`, the typed operations a front end calls.
- `cli`: the command line over the API.
- `web`: the web view over the API. The CLI does not depend on it.

The Lean library is in `lean/FrFlow/`. The MCP server is on the branch
`web-view`, which will become a separate repository.

## Measurements

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
