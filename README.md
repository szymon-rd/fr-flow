# FrFlow

FrFlow builds a system as a tree of requirements, proven in Lean and decided by
a person: one root, the idea's purpose, refined by small statements in the
domain's words down to contracts on the code. Every drift from what was decided
is shown, also when agents build most of a large project.

## Problem

Agents add logic step by step, with no stated relation to the intent. A program
is the visible part of a theory its programmers hold (Naur, 1985): why it is as
it is, and how it maps to the world. With agents, the developer often never
builds that theory, and the agent loses it when its context is compressed.

## The method

The developer writes the idea in `IDEA.md`. An agent writes Scala nodes; Lean,
generated from the Scala, proves each step. The nodes form a DAG:

- **One root**: the purpose in one sentence, stated as *exactly* (what users
  can do and what must never happen, together), so a system that does nothing
  does not meet it.
- **Parts**: every other node is a part of the nodes above it
  (`.under(parents*)`), and may be a part of several. A parent's parts,
  together, prove it; each is needed; they do not contradict each other. A node
  says one thing, in one sentence of the developer's domain words. A node that
  only restates its parent is not a node. A parent has 2 to 5 parts.
- **A shared vocabulary**: the root speaks in general terms, left open
  (`Opaque` types, `Param` terms, each saying what it means). Decided
  definitions bring in the domain (grants, sessions, tokens) as it is needed.
  Each term has one meaning and at most one definition in force.

| Kind | Written as | Lean |
|---|---|---|
| claim | `Node.claim(id, statement, why)(formula)`; the one with no parents is the root | proven from its parts (`complete`) |
| invariant | `Node.invariant[A, B](id, statement, why)(rule)`, kept by contracts with `.keeps(inv)(view)` | a claim whose parts are its keepers |
| contract | `Node.contract(op)(id, statement, why)(post)` on an operation `op: Param[(A, B) => R]` | every call of `op` meets `post`; a `define` attached is proven against it (`impl`) |
| assumption | `Node.assumption(op)(...)(post)`, or `Node.assumption(id, statement, why)(formula)` | trusted, not proven: what the outside does (a database, a clock), or a fact of the world |
| definition | `Node.definition(id, statement, why)(Type := of[T], term := expr, ...)` | fixes terms of the vocabulary; decided, not proven |
| design | `Node.design(id, statement, why)(files*)` | none: governs code no proof covers |

`.replaces(other)` marks an alternative: accepting one rejects the other. Two
definitions of one term are alternatives too.

From `examples/auth`, the smallest example:

```scala
val accessExactly = Node.claim("AccessExactly",
  "A user gets access to a resource exactly when they are signed in and authorized for it.", why = "...")(
  forall((u: User.T, r: Resource.T) => access(u, r) == (signedIn(u) && authorized(u, r))))
val decisionContract = Node.contract(admit)("DecisionContract", "...", why = "...")((token, path, decision) => ...)
  .under(tokenNamesHolder, accessNeedsGrant, grantLetsIn)
  .examples(grants.bind(...), sessions.bindTable(Map("t1" -> UserId("alice"))))(expect(...), reject(...))
val knowledge = KnowledgeBase("Auth", idea = "IDEA.md")(accessExactly, identities, grantTable, ..., inMemorySessions)
  .implementProven(decisionContract)(admitted, SessionStore(grants.value.toSet, sessions.value).decide)
```

The contract is a part of the root's three parts. `admitted` is a `define` that
Lean proves meets it; `SessionStore` is the code that runs, checked against it.

## Who decides

The developer decides every node, once. The agent proposes, with a `why` and
examples, often with alternatives; no command of the agent's decides.
`.frflow/ledger.json` holds each decision: who, their reason, the alternatives
rejected, the commit, a signature, and the node's decision before it.

- **A parent decides its parts.** What a node says includes the list of its
  parts, shown with whether Lean shows each needed, `complete` and `clash`.
  Adding or removing a part puts the parent up for review.
- **Order.** A proposal waits until its parents and the definitions it uses are
  accepted.
- **Mechanical decisions.** A node under review, not a definition or a design
  node, where nothing it says itself changed and Lean proves it again (and new
  parts make it, none shown not needed, no clash): one batch, `confirm`.
- **Signing.** Each decision is signed with the developer's key, kept outside
  the repository (`~/.config/frflow/signing.key`, or `FRFLOW_KEY`); its public
  key is committed as `.frflow/keys/NAME.pub`. A decision no filed key signed fails `status`.

## Drift

One rule: a decision binds a person's reason to the hash of what they saw.
Whatever moves under it puts the node back up for review, with the cause:

| Cause | What moved | Shown as |
|---|---|---|
| `self` | what the node says: statement, formula, `why`, examples, the terms and types it uses, kept invariants, implementation source; its section of the idea | a line diff per field |
| `above` | the meaning of a parent, of a definition it uses, or of a contract its code calls | the diff of what moved |
| `parts` | its list of parts | the parts added and removed |
| `code` | the files it governs: a plain implementation, a design node's files | a git diff since the decision's commit |
| `revisit` | the developer said a change above may affect it | their reason |
| `merged` | two branches decided it, and the merge kept both | both decisions |

A change above a shared node reviews it once; a new part reviews its parents
only. Rewording a `why` or a statement whose formula is unchanged does not
cascade below; a change of formula does. Accepting a change lists every
decision that rests on it, with its reason: the developer marks those it may
affect (`revisit`). A decision is refused if the node moved since the developer
looked at it, or if its reason is not a few words.

## What Lean proves

For each node N with parts C1..Cn, over the open terms they mention, with every
definition in force applied:

| Obligation | Statement | Fails when |
|---|---|---|
| `complete` | C1 → … → Cn → N | not proven: the parts do not make N (open) |
| `needed_C` (n ≥ 2), tried | N without C | Lean proves it: C is not needed for N |
| `vacuous` (n = 1), tried | N, with no hypothesis | Lean proves it: N says nothing its part adds |
| `restates` (n = 1), tried | N → C1 | Lean proves it: N says what its part says (a limit, not a failure) |
| `clash`, tried | C1 → … → Cn → False | Lean proves it: the parts contradict each other (failed) |
| `unsat` (every claim), tried | ¬ N | Lean proves it: no world meets N (failed) |
| `idle` (the root), tried | the root, every operation doing nothing (`[]`, `none`, `False`, its input unchanged) | Lean proves it: the root does not say what users can do |

`complete` is proven by `frflow_auto` or by hand. The tries use automation with
a small budget, so they catch only what it can show. Then:

- **Composition.** Each node gets `holds`: the leaves below it imply it.
  `root_impl` states the root of the code (every operation with a proven
  `define` replaced by it) from the assumptions alone: the trusted base.
- **Implementations** written as a `define` meet their contract (`impl`),
  proven from the promises of the operations the code calls, not their code.
- **Invariants.** A rule stated once over pairs (a reader, a record shown to
  them). Every contract in its scope keeps it (`.keeps(inv)(view)`) or says why
  it is exempt (`.exempt`). The invariant is proven from its keepers; for a
  rule about a domain type, `cover_X` proves the view lists every such value.
- **Examples, both ways.** Lean evaluates each example whose parameters are
  values (or `bindTable` lookups), and probes near them: it must prove what
  Scala computes and not its opposite. An expectation
  (`node.expects(statement)(formula)`) is proven from the node.
- **State.** A run is `es.foldLeft(init)(step)`; the library (`FrFlow.always`,
  `simulates`, `tracks`) proves properties of every run.
- **Authored proofs** (`lean/Proofs/<KB>/<Node>.lean`) state exactly the
  generated obligation and have their axioms audited (`sorry` fails). A
  hand-proven `complete` on a node nothing witnesses also needs `feasible`:
  some world meets all the parts.

**Checked by running.** Examples run against the contract and the
implementation, which also runs on every combination of the examples' inputs.
In production, `service` binds the operations to their code and checks every
result against the contract and its invariants (or `checkedBy`, a cheaper check
proven to follow from the post), raising `ContractViolation`.

**Effects are assumptions.** A database or a clock is an assumption on an
operation; the proven code is proven from its promise. The adapter (SQL) is
checked against a proven `define` (`implementProven(assumption)(define, sql)`)
on the examples, on varied data and on every call. In `examples/crm`, a seeded
SQL bug (a dropped `WHERE`) is stopped this way while every proof still holds.

## What is trusted, and the limits

Lean proves the nodes consistent with each other, and the root of the code; the
developer decides that they are the right theory. Trusted:

- the assumptions (the hypotheses of `root_impl`): checked where they can be;
- the Scala-to-Lean translation, cross-checked on the examples and on probes
  near them; it refuses what it cannot translate faithfully (`Int` arithmetic);
- that parameters hold the data they are said to mean, and that every path to
  the data goes through `service`: design nodes are reviewed, never proven;
- the signing key, kept outside the repository the agent edits;
- the model's program. FrFlow runs it to read it, so the gate stops drift, not
  an agent that writes code to subvert FrFlow.

Limits: the tries are one-sided. Examples with function-valued parameters
(other than `bindTable`) are not evaluated in Lean. Running covers the examples
and their combinations, not every input. Ordering, liveness, and effects outside
a pure core behind `service` are not covered. Maps and sets cannot be iterated.

## Usage

Requirements: JDK 17+, sbt, and Lean 4.35.0 (`lake` on the PATH, or
`FRFLOW_LAKE`). `bin/frflow PROJECT COMMAND` runs a project's CLI
(`bin/frflow auth tree`), compiling with sbt on first use and after a change.
`--help` lists the commands. `sbt test` runs the tests.

| | command | what it does |
|---|---|---|
| developer | `tree [NODE]` | the DAG from the root (or below NODE): status, kind and state when they say something, statement |
| | `show NODE`, `diff NODE` | a node in about a screen; what changed since it was decided |
| | `inbox` | what waits for whom, then the summary |
| | `review` | decide what waits, parents first: `[a]ccept [r]eject [s]kip [v]iew [q]uit [?]ask` |
| | `accept NODE...`, `reject NODE`, `confirm`, `revisit NODE`, `gone NODE` | one decision, with `-m REASON`; shown and confirmed on a terminal, `--yes` without one |
| | `ask NODE TEXT`, `ask --idea TEXT`, `close REQUEST...` | ask the agent for a change; close an answer read |
| agent | `inbox`, `context NODE`, `find WORDS\|PATH` | what to do; everything on a node (`show --full`); where a change belongs |
| | `render`, `check [NODE]`, `scaffold NODE` | Lean and `.frflow/kb.json`; prove what changed; stubs for what the last check left open |
| | `status`, `ci` | the tree, the summary and the warnings; exit 1 unless the knowledge base is complete (`ci` checks first) |
| | `answer REQUEST\|NODE TEXT` | reply to a request, or tell the developer of work they did not ask for |

On a terminal the output has colors and Unicode and is cut to its width.
`--plain`, `NO_COLOR` or a pipe give plain ASCII, not cut. `--json` on tree,
show, inbox, status and check prints the typed value, each node in brief. Exit
codes: 0 fine; 1 not complete, or a decision refused; 2 a usage error (an
unknown node too); 3 no Lean. The agent's rules are in
[`.claude/skills/frflow/SKILL.md`](.claude/skills/frflow/SKILL.md).

`status` exits 1 unless every node is accepted, nothing is left unproven, no
node is gone, and there is no warning: a decision not signed by a developer
key, a source file governed by two nodes or by none, a section of the idea no
node names, a contract none of whose examples Lean evaluates.

Committed: the Scala, `IDEA.md`, `.frflow/` (ledger, keys, requests) and
`lean/Proofs`; the rest is derived. CI runs `ci`, caching `.frflow/checks.json`
and `lean/.lake` by branch: only what changed is proven again. `bench/`
measures FrFlow as a project grows.

## Examples

The example ledgers are decided by an agent playing the developer.

- **`examples/auth`**: access control, shown above. Its code is proven, and
  `root_impl` trusts nothing.
- **`examples/keycloak`**: a small Keycloak-like server (realms, sign-in, token
  introspection, sign-out) over HTTP. Its sessions are proven to follow the
  history of requests (`FrFlow.tracks`).
- **`examples/crm`**: a multi-tenant CRM on SQLite, with an HTTP API and an
  expiry job. Nothing a user does changes another company's records. The
  alternative that relied on the job's schedule is rejected in the ledger.

## New project

A project is a directory beside the examples (here `examples/library`):

1. `IDEA.md`: a title, a lead paragraph, `## ` sections, and `## Not modelled`.
2. `lazy val library = example("library")` in `build.sbt` (and the project in
   `root`'s `aggregate`), then `sbt reload`.
3. The model in `src/main/scala/library/`, ending with the knowledge base and
   its command line (with several mains, set `Compile / run / mainClass`):
   ```scala
   val knowledge = KnowledgeBase("Library", idea = "IDEA.md")(lendsExactly, ...)
   object libraryCli extends frflow.cli.FrFlowApp(knowledge, root = "examples/library")
   ```
4. `bin/frflow library render` creates `lean/` (its `lakefile.toml`, toolchain
   and the generated Lean); then `check` and `status`.

## Modules

One sbt subproject each, under `modules/`:

- `protocol`: the data crossing modules and files (snapshot, review, ledger, checks, requests), with JSON codecs.
- `model` (package `frflow`): nodes and knowledge bases; `Opaque`, `Param`, `define`; the macro; examples, probes, `service`.
- `lean`: the Lean of a knowledge base, and reading Lean's output.
- `ledger`: review states and the decision rules; the reports; the stores, keys and signatures.
- `check`: render and check (running `lake`), the snapshot, status, scaffold, git.
- `api`: `FrFlowApi`, the typed operations a front end calls (`LiveApi` over the project on disk).
- `cli`: the command line over the API: `FrFlowApp`, the views, the review.

The Lean library is in `lean/FrFlow/`, and the design in [`docs/DAG.md`](docs/DAG.md).
The web view and the MCP server are on the branch `web-view`, which will become a separate repository.
