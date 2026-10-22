# FrFlow

FrFlow builds a system as a tree of requirements, proven in Lean and decided by
a person: one root, the idea's purpose, refined by small statements in the
domain's words down to contracts on the code. Every drift from what was decided
is shown. The aim is to keep the theory of the system and stop drift, also when
agents build most of a large project.

## Problem

Agents add logic step by step, with no stated relation to the intent, so
correctness and design coherence cannot be tracked. A program is the visible
part of a theory its programmers hold (Naur, 1985): why it is as it is, and
how it maps to the world. With agents, the developer often never builds that
theory, and the agent loses it when its context is compressed. A large system
needs its theory to outlive every context window.

## The method

The developer writes the idea in `IDEA.md`: a title and a lead paragraph (the
purpose), `## ` sections for its concerns, and `## Not modelled`. An agent
writes Scala nodes; Lean, generated from the Scala, proves each step. The nodes
form a DAG:

- **One root**: the purpose in one sentence, stated as *exactly* (what users
  can do and what must never happen, together), so a system that does nothing
  does not meet it.
- **Parts**: every other node is a part of the nodes above it
  (`.under(parents*)`), and may be a part of several. A parent's parts,
  together, prove it; each is needed; they do not contradict each other. A node
  says one thing, in one sentence of the developer's domain words; a node that
  only restates its parent is not a node. A parent has 2 to 5 parts; more asks
  for an intermediate concept.
- **A shared vocabulary**: the root speaks in general terms (users, resources,
  access), left open (`Opaque` types, `Param` terms, each saying what it means
  in the world). Decided definitions bring in the domain (grants, sessions,
  tokens) as it is needed. Each term has one meaning and at most one
  definition in force.

| Kind | Written as | Lean |
|---|---|---|
| claim | `Node.claim(id, statement, why)(formula)`; the one with no parents is the root | proven from its parts (`complete`) |
| invariant | `Node.invariant[A, B](id, statement, why)(rule)`, kept by contracts with `.keeps(inv)(view)` | a claim whose parts are its keepers |
| contract | `Node.contract(op)(id, statement, why)(post)` on an operation `op: Param[(A, B) => R]` | every call of `op` meets `post`; code attached is proven against it (`impl`) |
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

val grantTable = Node.definition("GrantTable", "A user is authorized for a path when a grant names that user and that path.",
  why = "...")(authorized := ((u: UserId, p: Path) => grants.value.contains(Grant(u, p))))

val accessNeedsGrant = Node.claim("AccessNeedsGrant",
  "A request is admitted on behalf of a user only if a grant names that user and the path.", why = "...")(
  forall((t: String, p: Path) => admit(t, p).forall(u => grants.value.contains(Grant(u, p))))).under(accessExactly)

val decisionContract = Node.contract(admit)("DecisionContract", "...", why = "...")((token, path, decision) => ...)
  .under(tokenNamesHolder, accessNeedsGrant, grantLetsIn)
  .examples(grants.bind(...), sessions.bindTable(Map("t1" -> UserId("alice"))))(expect(...), reject(...))

val knowledge = KnowledgeBase("Auth", idea = "IDEA.md")(accessExactly, identities, grantTable, ..., inMemorySessions)
  .implementProven(decisionContract)(admitted, SessionStore(grants.value.toSet, sessions.value).decide)
```

The root has three parts, and one contract is a part of all three; four
definitions say what users, resources, authorization, signing in and access are
in the domain. `admitted` is a `define` Lean proves meets the contract;
`SessionStore` is the code that runs, checked against it.

## Who decides

The developer decides every node, once, in the browser; the agent proposes,
with a `why` and examples, often with alternatives (`replaces`), through MCP
and the CLI, and no tool of the agent's decides. `.frflow/ledger.json` holds
each decision: who, their reason, the alternatives rejected, signed; it is
append-only.

- **A parent decides its parts.** What a node says includes the list of its
  parts. The browser shows them as one table (each part's statement, whether
  Lean shows it needed, its status, then `complete` and `clash`; on the root
  also `idle`, `root_impl` and the trusted list): "these parts make it".
  Adding or removing a part puts the parent up for review.
- **Order.** A proposal waits until its parents and the definitions it uses are
  accepted; the inbox lists ready nodes first.
- **Mechanical decisions** (`Decisions.mechanical`): a node under review, not a
  definition or a design node, where nothing it says itself changed, that Lean
  proves again with its examples passing (if its parts changed: they make it,
  each needed, no clash). The browser offers them as one batch.
- **Signing.** The browser server signs each decision with the developer's
  key, kept outside the repository (`~/.config/frflow/signing.key`, or
  `FRFLOW_KEY`); `frflow serve --as NAME` files its public key as
  `.frflow/keys/NAME.pub`, to commit. A decision not signed by a key there is a
  warning, so `status` fails.
- **Owners.** `owner = "ana"` on a node: only she decides it, and every node
  whose first parent she owns, recursively; a decision by anyone else is a
  warning.
- **Other knowledge bases.** `kb.uses(other, "../other")(contracts*)` brings
  another project's contracts as leaves, decided there (its ledger and keys)
  and proven again here. A node under one of them is refused: call its
  operation instead.

## Drift

One rule: a decision binds a person's reason to the hash of what they saw.
Whatever moves under it puts the node back up for review, with the cause:

| Cause | What moved | Shown as |
|---|---|---|
| `self` | what the node says: statement, formula, `why`, examples, the terms and types it uses, kept invariants, implementation source; its section of the idea | a word diff |
| `above` | the meaning of a parent, of a definition it uses, or of a contract its code calls | the diff of what moved |
| `parts` | its list of parts | the parts added and removed |
| `code` | the files it governs: a plain implementation, a design node's files | a git diff since the decision |
| `revisit` | the developer said a change above may affect it | their reason |
| `merged` | two branches decided it, and the merge kept both | both decisions |

A change above a shared node reviews it once, whatever the number of paths; a
new part reviews its parents only. Rewording a `why`, adding an example, or
rewording a statement whose formula is unchanged does not cascade below (out of
Lean, `formal = false`, rewording does); a change of formula does. Accepting a
change lists every
decision that rests on it, however far down, each with its reason; the
developer marks those it may affect (`revisit`) and confirms by name those that
moved only because of it. A reason that says when to revisit it ("revisit if
…", "fine until …") must be answered by name, also above a new node. A decision
is refused if the node moved since the developer looked at it, or if its reason
is not a few words. A decided node removed from the model is listed as gone
until the developer agrees, or accepts it as "Renamed to X".

## What Lean proves

For each node N with parts C1..Cn, over the open terms they mention, with every
definition in force applied:

| Obligation | Statement | Fails when |
|---|---|---|
| `complete` | C1 → … → Cn → N | not proven: the parts do not make N (open) |
| `needed_i` (n ≥ 2), tried | N without Ci | Lean proves it: Ci is not needed for N |
| `vacuous` (n = 1), tried | N, with no hypothesis | Lean proves it: N says nothing its part adds |
| `clash`, tried | C1 → … → Cn → False | Lean proves it: the parts contradict each other (failed) |
| `unsat` (every claim), tried | ¬ N | Lean proves it: no world meets N (failed) |
| `idle` (the root), tried | the root, every operation doing nothing (`[]`, `none`, `False`, its input unchanged) | Lean proves it: the root does not say what users can do |

`complete` is proven by `frflow_auto` or by hand; the tries use automation with
a small budget, so they catch only what it can show. Then:

- **Composition.** Each node gets `holds`: the leaves below it (contracts,
  assumptions, claims without parts) imply it; a shared node is proven once.
  `root_impl` states the root of the code (every operation with a proven
  `define` replaced by it) from the assumptions alone: its hypotheses are the
  trusted base, shown by `status` and in the browser.
- **Implementations** written as a `define` meet their contract (`impl`),
  proven from the promises of the operations the code calls, not from their
  code: each contract is proven once.
- **Invariants.** A rule stated once over pairs (a reader, a record shown to
  them). Every contract in its scope keeps it (`.keeps(inv)(view)`, the pairs a
  call shows) or says why it is exempt (`.exempt`); so does each design node in
  the scope. The invariant is proven from its keepers; for a rule about a domain
  type, `cover_X` proves the view lists every such value.
- **Examples, both ways.** Lean evaluates each example whose parameters are
  values (or `bindTable` lookups), and probes near them: it must prove what
  Scala computes and not its opposite. An expectation
  (`node.expects(statement)(formula)`) is proven from the node.
- **State.** A run is `es.foldLeft(init)(step)`. The library proves properties
  of every run: `FrFlow.always` (a property every step keeps),
  `FrFlow.simulates` (a step mirroring an abstract one), `FrFlow.tracks` and
  `tracks_eq` (the state follows the history of events), `FrFlow.run_snoc`.
- **Authored proofs** (`lean/Proofs/<KB>/<Node>.lean`, shared lemmas in
  `Lemmas.lean`) state exactly the generated obligation, use a few allowed
  commands and imports, and have their axioms audited (`sorry` fails). A
  hand-proven `complete` with no proven code below also needs `feasible`: some
  world meets all the parts, so a proof cannot rest on a contradiction.

Lean is the default. Where the Lean subset cannot say a node, or a proof costs
more than it gives, the node opts out with `formal = false`: its split is
decided by reading, and its examples and `service` still run.

**Checked by running.** Examples run against the contract and the
implementation, which also runs on every combination of the examples' inputs.
In production, `service` checks every result against the contract and its
invariants (proven code too), or raises `ContractViolation`; it binds the other
operations to their code and each defined term to its definition, and refuses
to start if a parameter it reads is unbound. Where the post reads all the data,
`checkedBy` gives a cheap check of the result alone, proven to follow from the
post. An assumption on a fact that can be computed is checked when the service
starts and when a value it reads changes.

## Effects: assumptions

A database, an HTTP client or a clock is an assumption on an operation, whose
post says what the outside is trusted to do. The proven code calls the
operation's `Param` and is proven from that promise; the adapter (SQL) is plain
code with a proven `define` as its reference
(`implementProven(assumption)(define, sql)`), checked against it on the
examples and on varied data, and by its `checkedBy` on every call. Wiring that
calls an adapter past `service`, or changes the outside past an assumption, is
a warning. In `examples/crm`, a seeded SQL bug (a dropped `WHERE`) is stopped by
the check while every proof still holds, and so is a write the database drops.
Measured before the DAG rework (`crm/Test/runMain crm.benchReads 100000`): the
checks add about 1% to a read at 100,000 records.

## Status and CI

`status` exits 1 unless every node is accepted, nothing is left unproven (one
list per node, `Decisions.unproven`: its check, its split, examples,
invariants, implementation, expectations, `root_impl`, `idle`, and a claim
nothing below proves), no node is gone, and there is no warning: a decision
unsigned or not by the owner; a source file governed by two nodes or by none;
code in a model file that is none of the model; a section of the idea no node
names; a statement naming a rejected node; a formal contract none of whose
examples Lean evaluates. It prints the tree, the trusted list, and how far the
proofs reach.

`ci` is what CI runs: `check`, then `status`; it also fails when a decision in
the ledger where the branch left its base (`FRFLOW_BASE`, by default
`origin/HEAD`) is gone. The results (`.frflow/checks.json`) are not committed;
keep them and Lean's build in the CI's cache, keyed by branch
(`<kb>/.frflow/checks.json`, `lean/.lake`, `<kb>/lean/.lake`): each result is
recorded with the hash of what it proved, so only what changed is proven again.
A result read from the cache is as trusted as the cache.

## Large projects

The theory lives in files, not in an agent's context: `context(node)` gives
what bears on a node (its idea section, vocabulary and definitions, ancestors
with their reasons, co-parts, parts, rejected alternatives, what moved), and
`find` searches nodes, reasons, rejected options and the idea, so an agent
extends the theory instead of forking it. Every file has one owner, and a
change reviews only what rests on it. `check` runs nodes side by side in levels
(`FRFLOW_THREADS`); a Lean timeout is checked again. Enable the ledger's merge
driver once per clone (a node both branches decided is decided again):

```sh
git config merge.frflow-ledger.driver "bin/frflow merge-ledger %O %A %B"
```

**Measured.** `python3 bench/generate.py N` writes `examples/scale`: one root
over N services, grouped five by five (a group: five service claims and the
floor invariant their contracts keep; past five groups, areas of five groups),
each group's promise one defined word, so no statement grows with N. Each
service is a claim with two or three parts and a contract with proven code;
every fifth service's code calls the previous one's, and every tenth service
has a split proven by hand (`sbt "scale/run check"`). On a 4-core container:

| nodes | cold `check` | one code change | one claim change | one definition change | `status` |
|---|---|---|---|---|---|
| 103 | 92 s | 14 s | 15 s | 45 s | 2.2 s |
| 305 | 234 s | 19 s | 21 s | 125 s | 4.3 s |

(`bench/measure.sh 20 60`. The code change is one service's code; the claim change strengthens one
service's part; the definition change is the limit every bounded service keeps, about a third of the
nodes.)

A cold check proves each level in one Lean build (about 0.85 s a node); after
that, only what a change reaches is proven again: a code change, its contract
and the root; a claim change, the claim and the nodes above it; a definition
change, every node that uses the term. `ci` also proves again a random 5% of the
results it reads from the cache (`FRFLOW_VERIFY`), with their Lean build
removed first, so a bad results file or build cache is found.

## What is trusted, and the limits

Lean proves the nodes consistent with each other, and the root of the code; it
does not say they are the right theory. That is the developer's decision.
Trusted:

- the assumptions (the hypotheses of `root_impl`): checked where they can be, not proven;
- the Scala-to-Lean translation, cross-checked on the examples and on probes
  near them (`Generate.near`: boundary numbers, shorter and reversed lists,
  one field changed), each run in Scala and evaluated in Lean; it refuses what
  it cannot translate faithfully (`Int` arithmetic, for one);
- that parameters hold the data they are said to mean, and that every path to
  the data goes through `service`: design nodes are reviewed, never proven;
- the signing key: run the browser server outside the repository the agent edits;
- the model's program. FrFlow runs it to read it, so the gate stops drift, not
  an agent that writes code to subvert FrFlow. Every node's definition as
  written is decided, and every source file has a reviewed owner.

Limits: the tries (`needed`, `clash`, `unsat`, `idle`) are one-sided: what
automation cannot show is not caught. Examples with function-valued parameters
(other than `bindTable`) are not evaluated in Lean; running covers the examples
and their combinations, not every input; ordering, liveness and effects outside
a pure core behind `service` are not covered. Maps and sets are functions in
Lean: what needs iterating them (sizes, all keys) cannot be said.

## Examples

**`examples/auth`**: access control, shown above. One root, three parts, four
definitions, one contract under all three parts; its code is proven, and
`root_impl` trusts nothing.

**`examples/keycloak`**: a small Keycloak-like server (realms, sign-in, token
introspection, sign-out, administrators enabling users), served over HTTP
(`sbt "keycloak/runMain keycloak.serveRealms 8080"`). Its DAG:

| Node | Its parts |
|---|---|
| **RealmAccess** (root): a realm's application accepts a token as a user's, with their roles, exactly when they signed in, have not signed out, and are enabled | NoUnauthorizedAccess, SignedInAreAccepted |
| NoUnauthorizedAccess | OnlyTheSignedIn, DisabledHaveNoAccess, RolesAsGranted |
| SignedInAreAccepted | SessionsMirrorSignIns, AccountsAsAdministered, OneSignInPerToken, Introspect |
| OnlyTheSignedIn | SessionsMirrorSignIns, RealmIsolation (invariant), AnswersNameASession |
| DisabledHaveNoAccess; RolesAsGranted | AccountsAsAdministered, Introspect |
| SessionsMirrorSignIns | FreshTokens (assumption), HandleRequest (contract) |
| AccountsAsAdministered | HandleRequest |
| OneSignInPerToken | FreshTokens |
| RealmIsolation; AnswersNameASession | Introspect (contract) |

Definitions: Identities, Accounts, SignInHistory, ServerRun, ReferenceTokens.
Design: ServiceWiring and HttpApi. `SignInHistory` says what being signed in
means from the history of requests alone; `SessionsMirrorSignIns` proves the
server's sessions follow it (`FrFlow.tracks`). `root_impl` trusts `FreshTokens`
and the two assumptions on the store the code calls, `StoreKeepsState` and
`SessionLookup`.

**`examples/crm`**: a multi-tenant CRM on SQLite, with an HTTP API and an
expiry job. Its root (`SharedCrm`) says what users find, add, share and
unshare, and that nothing a user does changes another company's records; ten
definitions introduce the domain. Its parts: `Visibility` (the two screens and
the invariant `NoCrossTenantRead`), `WritesTakeEffect`, `WritesInCompany` (with
`StoreConsistent`, by `FrFlow.always`), and `SharesExpire`. `root_impl` trusts
the two assumptions on the database.

The example ledgers are decided by an agent playing the developer.

## Usage

Requirements: JDK 17+, sbt, and Lean 4.35.0 (`lake` on the PATH, or
`FRFLOW_LAKE`).

```sh
bin/frflow serve examples             # the browser, where the developer decides
bin/frflow mcp examples               # the MCP server for agents (see .mcp.json)
sbt test                              # unit tests, and Lean tests when lake is available
sbt "auth/run render"                 # Lean and the snapshot .frflow/kb.json
sbt "auth/run check"                  # prove what changed, record the results
sbt "auth/run status"                 # exits 1 unless decided, proven and passing
sbt "auth/run ci"                     # what CI runs: check, then status
```

The browser draws the DAG from the root, each node under its first parent
with "also under" its others, definitions in their own row, assumptions marked
trusted. A node's pane shows its parents (each with its split and co-parts),
the node (its formula, vocabulary and examples), and its parts. Every node has
one "Ask for a change" box: the node is then with the agent, not waiting for
you, until the agent answers or changes it. The agent's
rules are in [`.claude/skills/frflow/SKILL.md`](.claude/skills/frflow/SKILL.md).

Committed: the Scala, `IDEA.md`, `.frflow/` (ledger, keys, requests) and
`lean/Proofs`; the rest is derived.

### New project

A project is a directory beside the examples (here `examples/library`, its
knowledge base `Library`):

1. `IDEA.md`: a title, a lead paragraph (the purpose), `## ` sections, and
   `## Not modelled`.
2. `frflow.json`, which tells the browser and MCP how to run its CLI and which
   files are its sources:
   ```json
   { "name": "Library", "run": ["sbt", "--client", "library/run {args}"], "cwd": "../..",
     "sources": ["src/main/scala", "IDEA.md", "lean/Proofs"] }
   ```
3. A line in `build.sbt` (and the project in `root`'s `aggregate`), then
   `sbt reload`:
   ```scala
   lazy val library = example("library")
   ```
4. The model in `src/main/scala/library/`, ending with the knowledge base and
   its command line (with several `@main`s, set `Compile / run / mainClass`):
   ```scala
   val knowledge = KnowledgeBase("Library", idea = "IDEA.md")(lendsExactly, ...)
   @main def libraryCli(args: String*): Unit = sys.exit(knowledge.cli(args, root = "examples/library"))
   ```
5. `sbt "library/run render"` creates `lean/` (its `lakefile.toml`, toolchain
   and the generated Lean); then `check`, and `bin/frflow serve examples` shows
   it beside the others.

## Layout

```
docs/DAG.md             the design: one root, parts, the vocabulary, obligations, decisions
lean/FrFlow/            the Lean side: frflow_auto, frflow_intro; run and list lemmas (always, simulates, tracks)
core/                   the Scala library
  Node, Model, Lift     nodes and knowledge bases; Opaque, Param, define; the macro from Scala to Lean
  Generate, Lean        Lean generation; running lake, axiom audits, the proof-file filter
  Decisions             decision states and rules, shared by the CLI, browser and MCP
  Ledger, Signing       the decision record and its merge; keys and signatures
  Workflow, Cli, Git    render, check, context, status; the command line; diffs
examples/               auth, keycloak, crm
bench/                  the scale benchmark and the evidence plan
tools/                  the browser server and UI, the MCP server, the merge driver
bin/frflow              runs them
.claude/skills/frflow   the agent skill
```
