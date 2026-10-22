# FrFlow

FrFlow builds a system as a chain of **proven logical refinements**, from the
idea down to the code, with every step decided by a person and every drift
from those decisions shown. It is an experiment in doing for software what
some hardware projects did: refine a specification step by step, and prove
each step, now that agents can write the models and the proofs.

## Problem

- **Uncontrolled refinement.** Agents add logic incrementally, without an
  explicit relation to the intent, so correctness and design coherence cannot
  be tracked.
- **Lost theory** (Naur, *Programming as Theory Building*, 1985). The program
  is the visible part of a theory held by its programmers: why it is the way it
  is, how it maps to the world, what would have to change if the world did.
  With agents, the human often never builds that theory, and the agent loses
  it when its context is compressed.
- **Scale.** A large system grown by many agents over many sessions needs its
  theory to outlive every context window, its cross-cutting rules to hold
  everywhere, and the developer's attention spent on choices, not on every
  change.

## The method

The developer writes the idea in `IDEA.md`. The knowledge is a **forest** of
Scala values: a tree under each root (one concern of the idea), and invariants
that cut across the trees. Lean, generated from the Scala, proves each step:

| Kind | Written as | Proven |
|---|---|---|
| root | `Node.root[M](id, statement, why, idea = "Section")(spec)` | it is the statement of one concern of the idea |
| refine | `parent.refine[M2](id, statement, why)(abs, spec)` | `spec m → parent.spec (abs m)` |
| instantiate | `parent.instantiate[M2](id, statement, why)(T := of[X], p := ...)` | its link holds by substitution (the parent's results, with its open terms fixed); Lean checks it builds |
| contract | `parent.contract[A, B, R](id, statement, why)(post).examples(...)(...)`, or `parent.contractVia[A, B, R](...)(abs)(post)` for a signature of its own | every function meeting `post` meets the parent (through `abs`) |
| implementation | `kb.implementProven(contract)(define {...})`, or `kb.implement(contract)(plain Scala)` | a `define`: every result meets the contract, and the root holds of it (`root_impl`); plain Scala: examples and run-time checks |
| invariant | `Node.invariant[A, B](id, statement, why)(rule)`; each contract `.keeps(inv)(view)` or `.exempt(inv, because)`; each design node `.exempt(inv, because)` | every pair the view lists meets the rule, from the contract's post; and the view lists all the result holds (see below) |
| design | `parent.design(id, statement, why)(files*)` | nothing: an architecture decision or a convention, decided and tracked |
| expectation | `node.expects(statement)(m => ...)` on a root, refine or contract | a consequence the developer expects of every model of the node, proven from its spec |
| reliance | `node.relies(other, why)` | nothing: `other` becomes part of what the node rests on (see Drift) |

So for a node, its **root theorem** holds: the root's statement is true of
every model of the node, through every link above it. With a proven
implementation, it is true of the code.

| What is recorded | Where |
|---|---|
| the idea, by concern (`## ` sections), and what it leaves out (`## Not modelled`, with a `### ` subsection per concern if needed) | `IDEA.md` |
| what each open term means in the world | `Opaque("User", "a person who uses the system")`, `Param(..., means)` |
| per node: statement, `why`, formal model, examples | the Scala source |
| per contract: what it does *not* promise, found mechanically | shown with the node |
| per node: who decided it, their reason, the alternatives rejected | `.frflow/ledger.json`, append-only, signed |

## Who decides

**The developer decides every node, in the browser.** The agent proposes
nodes, each with its reason and examples; the developer chooses one, with a
reason of their own, and the ledger keeps both and the rejected alternatives.
The tree is decided from the root down. The agent never writes the ledger.

**Mechanical decisions** hold no choice, and Lean proves again all there is
to prove: a refinement or contract whose link Lean proves and whose examples
pass, new with nothing beside it, or under review only because something above
it moved, only its proven implementation changed, or only the shape of a
domain type it uses changed (that last also for an instantiation or
invariant). Not mechanical: roots, instantiations, invariants, design and
informal nodes, a node beside alternatives, introducing terms or naming
invariants, a node once rejected or resembling a rejected one (compared with
bound variables renamed), a changed `why`, any other change to what a node
says, and code changes. The browser groups the mechanical nodes; the developer
accepts them in one batch, with one reason, signed like any other decision.

## Drift

**One rule: a decision binds a person's reason to the hash of what they saw;
whatever moves under it puts the node back up for review.** A node under
review says why:

| Cause | What moved | Shown as |
|---|---|---|
| `self` | the node: statement, `why`, sources, examples, the terms it introduces, the definitions and types it uses, the invariants it keeps, its implementation's source; for a root, its section of the idea and what is not modelled for it | a word diff against what was decided |
| `above` | the *meaning* of an ancestor, of an invariant it keeps, or of a node it relies on (rewording a `why` or adding an example does not cascade) | the diff of what moved |
| `code` | the files it governs: a plain implementation's, a design node's, anything `.governing` names | a git diff since the developer's last decision |
| `revisit` | the developer said a change above may affect it | their reason |
| `merged` | two branches decided it, and the merge kept both | both decisions |

A node removed from the model is listed as **gone** until the developer agrees.

`.relies(other, why)` makes another node, often of another concern, part of
what a node rests on, like its parent and the invariants it keeps: a change to
`other`'s meaning reviews the node (`above`), the node waits for `other`, and
accepting the change lists the node among the decisions below. A reliance
that leads back to the node is refused.

A change of meaning cascades by itself. A change that does not may still break
a reason written below ("revisit if we add exports"). So accepting a change
lists the decisions below with their reasons; the developer ticks those it may
affect (they are reviewed again), and those that moved only because of it are
confirmed by name. The reasons are where the conditions for revisiting are
written; this is where they are read.

A decision is refused if the node moved since the developer looked at it, and
needs a reason of a few words. Reviews caused by one change (nodes moved only
by the same ancestors, or changed only in the same definitions) are accepted
together, with one reason. A review can also be sent back to the agent as a
request.

**Every decision is signed.** The browser server signs each decision with the
developer's key, kept outside the repository (`~/.config/frflow/signing.key`,
or `FRFLOW_KEY`); public keys are committed in `.frflow/keys/`. The developer
key is the first one committed; another counts once a developer key certifies
it (in the browser), and a removed key is a warning. A decision without a
valid signature is a warning, so `status` fails; the browser lists it to
decide again, or to sign if it is the developer's. With no developer key, no
decision is signed and `status` fails ("no developer key"): start `frflow
serve` (it creates the key), commit `.frflow/keys/`, and sign there. An agent that
committed a key first would be the developer, so `status` names the key and
who first committed it, and CI should pin it (`FRFLOW_DEVELOPER_KEYS`). The
server takes decisions only from the page opened from the link it printed.

## What Lean proves, and how it is kept honest

- **Links:** each formal node implies its parent; an instantiation's link
  holds by substitution. Each obligation is stated by the generator, never by
  the agent.
- **Invariants:** the rule is stated once, over pairs (a reader and a record
  returned to them). Every contract in the invariant's `scope` (all, by
  default) whose result can hold what the rule is about (a record, or a store
  of records) keeps it, listing the pairs a call shows (`result.map(r => (user,
  r))`), or is exempt with a reason; so is every design node below a keeper.
  Lean proves the rule for every pair the view lists, from the post
  (`inv_X`); for a rule about a domain or opaque type, also that the view lists
  every such value the result holds (lists, options, tuples, case classes and
  enums unfolded; a recursive type fails), each with the call's input of the
  rule's first type when only one input has it (`cover_X`). So a view cannot
  leave out or mis-pair what the result shows, however a filter is hidden.
- **Implementations** written as a `define` are proven to meet their contract,
  and `root_impl` composes that with the chain: the root holds of the code.
- **Examples are evaluated in Lean.** On each example of a formal contract
  whose parameters are values, Lean (`simp`) must prove what Scala computes
  (the verdict of `post`, and a proven implementation's result) and not its
  opposite. A disagreement fails the node: the translation does not mean what
  the Scala does. An example Lean cannot evaluate is shown as unevaluated.
- **State.** A root over runs, `List[Event] => State` ("every state reached is
  consistent"), is refined by a step `(State, Event) => State` with `abs` the
  fold of the steps from the initial state; the link is proven by induction
  (`FrFlow.always`). The CRM's writes are modelled this way.
- **Expectations:** consequences the developer states (`expects`), proven from
  the node's spec, so the theory is tested, not only approved.
- **Authored link proofs need a witness:** `feasible` (some model meets the
  node), or a proven implementation at or below it, reached through no assumed
  link, with its `root_impl` proven; until then the link shows open. So a
  hand-written proof cannot rest on a contradiction.
- **Authored proofs** (`lean/Proofs/<KB>/<NODE>.lean`, shared lemmas in
  `Lemmas.lean`) state exactly the generated obligation, use only a few
  commands, import only `FrFlowGen.<KB>.Domain`, `FrFlowGen.<KB>.<Node>.Spec`,
  `FrFlow`, `Std`, `Init` and `Proofs.<KB>.Lemmas`, are replayed through the
  Lean kernel, and have their axioms audited (`sorry` anywhere fails).
- **Assumptions about the world are shown:** a top-level condition of a spec
  that never mentions the model.

**Saying nothing** is checked by statements `frflow_auto` tries to prove; one
it proves shows the node says nothing:

| Check | Catches | Result |
|---|---|---|
| `vacuous_<claim>` | a link, kept invariant or expectation that holds without the node's own statement (an invariant kept in name only) | that claim fails |
| `unsat` | a refinement or contract no model meets | the link fails |
| `rootTrivial` | the root holds of every model, decided by an `abs` or a substitution above | the link fails |
| `idle` | doing nothing (returning nothing, or the input unchanged) meets the contract | listed with what it does not promise |

Lean is the default. Where a link's proof costs more than it gives, it can be
**assumed** (`assume = true` on a refine, contract or `contractVia`): its spec
stays formal, so everything below is still proven against it, and Lean takes
the link as an axiom, allowed only under the root theorems (`root`,
`root_impl`), which name it; what is proven of the node itself (`impl`, `inv`,
`cover`, `expect`, `feasible`) rests on Lean's axioms alone. Where the subset
cannot say a node at all, it opts out with `formal = false`: its model stays
Scala, its examples and `service` still run, its link is decided by reading,
and everything below it is out of Lean too.

## Checked by running

- **Examples** run against the contract and the implementation; an
  implementation that always returns one value must fail one of them.
- **Every combination of the examples' inputs** runs through the
  implementation, against the contract and its invariants.
- **In production,** `service` checks every result against the contract and
  its invariants, and refuses to start if a parameter it reads is not bound.

## Status, for CI

`status` exits 1 unless every node is accepted by the developer, every formal
link, invariant and proven implementation is proven, every example passes,
and there is no warning:
- a committed version of the ledger, or the ledger now, changed or removed
  decisions of a version it follows (compared with every parent of a merge);
  a commit that does so (a revert, a deleted ledger) is a warning until the
  developer acknowledges it, with a reason;
- a decision not signed by a developer key, or no developer key at all;
- a file governed by two nodes;
- a source file no node governs (any file under `src/main`; a source file
  elsewhere in the project but `src/test`, `target`, `lean`, `.frflow`,
  `project`, `node_modules` and hidden directories; any source the build
  compiles, when it passes `-Dfrflow.sources`, as a project's build should:
  see the examples' `build.sbt`), or code in the model's file that is not the
  model;
- a section of the idea no root is decided against, when roots name sections;
- a contract that never reads a parameter its ancestors use, or a statement
  naming a rejected node;
- `.frflow/checks.json` committed (CI runs `check` before `status`).
- fewer contracts proven down to their code than the idea asks: a line
  `Proven code: N%` in IDEA.md (decided with the roots, like the rest of the
  idea) asks that at least N% of the contracts have a proven `root_impl`.

It notes the developer key and who first committed it, and which contracts
each invariant does not reach (by the type they return).

Structural problems (two parameters with one name, a contract or design node
in an invariant's scope that neither keeps it nor is exempt, a reliance that
leads back to the node) stop the CLI.

## Large projects, built by agents

- **The theory lives in files.** `context(node)` gives an agent what bears on
  a node: its root's section of the idea, the vocabulary it uses, the path from
  the root (latest reason first), what stands or was rejected beside it, what
  it relies on and what relies on it, the invariants, what moved, the
  decisions below, the obligation, and the last check's failures in full.
- **Before adding, find.** `find` names the nodes that govern a file or
  mention a concern, so an agent extends the theory instead of forking it.
- **Every file has one owner**, or `status` fails. The model itself may span
  several files (one per concern, say); each holds only the model.
- **Cross-cutting rules are stated once**, and a new contract or design node
  cannot skip one silently: it keeps it or says why not.
- **Concerns are separate.** Each root names its section of `IDEA.md`; editing
  one section, or its `### ` subsection of Not modelled, reviews only its root.
- **Branches merge.** The ledger only grows; enable its merge driver once per
  clone (`git config merge.frflow-ledger.driver "bin/frflow merge-ledger %O %A %B"`,
  see `.gitattributes`). A node both branches decided is decided again.

## Example: a multi-tenant CRM (`examples/crm`)

```scala
val isolation = Node.root[(User.T, Record.T) => Boolean]("TenantIsolation",
  "A user sees a record only if it belongs to their company or was shared with their company.", why = "...")(
  shows => forall((u: User.T, r: Record.T) => shows(u, r) ==> visible(u, r)))

val readApi = isolation.refine[(User.T, Query.T) => List[Record.T]]("ReadApi",
  "Records are shown only as query results, and a query returns only records the user may see.", why = "...")(
  abs  = run => (u, r) => exists((q: Query.T) => run(u, q).contains(r)),
  spec = run => forall((u: User.T, q: Query.T) => run(u, q).forall(r => visible(u, r))))

val accounts = readApi.instantiate[(Account, Search) => List[CrmRecord]]("Accounts", "...", why = "...")(
  User := of[Account], Record := of[CrmRecord], Query := of[Search], Tenant := of[TenantId],
  tenantOf := ((a: Account) => a.tenant), owner := ((r: CrmRecord) => r.tenant),
  sharedWith := ((r: CrmRecord, t: TenantId) => shares.value.contains(Share(r.id, t))))
  .relies(crmWrites, "a share names one record by its id: ids are unique in every store the writes reach")

val noCrossTenantRead = Node.invariant[Account, CrmRecord]("NoCrossTenantRead",
  "No read returns a record of another company unless that company shared it with the reader's.", why = "...")(
  (reader, r) => r.tenant == reader.tenant || shares.value.contains(Share(r.id, reader.tenant)))

val readContract = accounts.contract[Account, Search, List[CrmRecord]]("ReadContract", "...", why = "...")(
  (user, query, result) => result.forall(r => store.value.contains(r) && matches(query, r) && ...))
  .examples(...)(expect(...), reject(...))
  .keeps(noCrossTenantRead)((user, query, result) => result.map(r => (user, r)))

val search = define { (user: Account, query: Search) =>
  store.value.filter(r => matches(query, r) && (r.tenant == user.tenant || shares.value.contains(Share(r.id, user.tenant))))
}

val knowledge = KnowledgeBase("Crm", idea = "IDEA.md")(isolation, readApi, accounts, readContract, readSideWiring, noCrossTenantRead, ...)
  .implementProven(readContract)(search)
```

Lean proves `ReadApi` implies the root, `ReadContract` implies `ReadApi` under
the CRM's meanings, that every record it returns keeps `NoCrossTenantRead`
(and that the view lists them all), and that `search` meets `ReadContract`:
tenant isolation holds of the code. Production reads through
`knowledge.service(readContract)(...)`, in a file the design node
`ReadSideWiring` governs.

Writes are a second concern of the idea, modelled as a state machine: the root
`WritesKeepStore` says the store starts consistent, every write keeps it so,
and a write changes only what its author's company may change. `applyWrite`, a
`define`, is proven to meet `WriteContract` by a short authored proof
(`lean/Proofs/Crm/WriteContract.lean`), so both concerns hold of the code.

`examples/auth` does the same for access control with a plain Scala
implementation. When it was built, the agent proposed two refinements of the
root: requests carry tokens (`Authenticated`), or the client names its user
(`ClientAsserted`). The developer chose `Authenticated`: *"a client's own claim
about who it is proves nothing. Revisit if requests come only from trusted
services."* The ledger keeps that reason and the rejected option. (The example
ledgers were written by an agent, to show the method.)

## The browser and the agent

```sh
bin/frflow serve examples     # the browser, where the developer decides: http://127.0.0.1:8765
bin/frflow mcp examples       # the MCP server, for agents (registered in .mcp.json)
```

The browser shows the forest (green links are proven), each node with its
examples (and whether Lean agrees), its link beside its parent's, its
invariants and reliances, the options rejected beside it, its reasons (latest
first), and **the decision**: choose between proposals, or see what moved and
accept it. The inbox lists what waits for the developer, mechanical decisions
in a batch of their own. The idea is edited there too; a save over an
`IDEA.md` changed since is refused, and a save starts a render.

The MCP tools are `inbox`, `context`, `render`, `check`, `answer`, `find` and
`scaffold`. None decides. The skill (`.claude/skills/frflow/SKILL.md`) gives
the agent its loop.

## What is proven, checked, and trusted

- **Proven by Lean:** every formal link, kept invariant (with its coverage)
  and `define` implementation, so every formal node's root theorem. The levels
  are consistent with each other; it does not say they are the right theory.
- **Checked by the examples:** that a contract means what its statement says,
  that the implementation does what was decided, in those cases, and that
  Lean computes what Scala does on them.
- **Enforced at run time:** every result of `service` meets the contract and
  its invariants, or `ContractViolation` is raised.
- **Decided by the developer:** every node, with its reasons, signed.
- **Trusted:**
  - the Scala-to-Lean translation, cross-checked only on the examples. Each
    local binder gets a Lean name of its own; it refuses a local named like a
    parameter, matching on `true`/`false`, type tests, function-typed fields,
    types that redefine equality, `Int`/`Long` arithmetic (it wraps in Scala:
    use `BigInt`) and division by anything but a literal;
  - parameters bound to the data the vocabulary says they mean;
  - that `abs` describes what the system does with the model;
  - every path to the data goes through `service` (the wiring is in a file a
    design node governs, and every change to it is the developer's);
  - the developer's signing key, which the agent must not be able to read: the
    tools (the browser server holds the key) are installed and run outside the
    repository the agent edits, on the developer's machine;
  - authored proof files, which Lean runs when checking (the filter is hygiene;
    the guarantee is the kernel replay and the axiom audit).
- **Limits:** the "says nothing" checks are one-sided (only what `frflow_auto`
  proves is caught); examples with function-valued parameters are not
  evaluated in Lean; local check results (`.frflow/checks.json`) are not
  evidence, so CI re-runs `check` from a clean checkout; properties over time
  other than what holds of every reachable state (ordering, liveness), and
  effects outside a pure core behind `service`, are not covered.

## Usage

Requirements: JDK 17+, sbt, and Lean 4.35.0 (`lake` on the PATH, or `FRFLOW_LAKE`).

```sh
sbt test                                  # unit tests, and Lean tests when lake is available
sbt "crm/run render"                      # Lean and the snapshot .frflow/kb.json
sbt "crm/run check"                       # prove the changed links, record the results
sbt "crm/run status"                      # exits 1 unless everything is decided, proven and passing (CI)
sbt "crm/run context ReadContract"        # what bears on a node, for agents and people
```

Committed: the Scala, `IDEA.md`, `.frflow/ledger.json`, `.frflow/keys`, the
requests and answers between the developer and the agent
(`.frflow/requests.json`), and `lean/Proofs`. Everything else is derived and
git-ignored. When a new FrFlow records content in a new shape, the node is
migrated (`migrate`), not decided again.

## Layout

```
lean/FrFlow/          the Lean side: the kernel and the frflow_auto tactic
core/                 the Scala library
  Model.scala         Opaque, Param, define
  Lift.scala          the macro: Scala lambdas to Lean
  Node.scala          nodes, invariants, examples, the knowledge base, service
  Decisions.scala     decision states and rules, shared by the CLI, browser and MCP
  Ledger.scala        the decision record, and its merge
  Signing.scala       the developer's keys, and the signatures of decisions
  Generate.scala      Lean generation
  Lean.scala          runs lake; reads Lean's messages and axiom audits; the proof-file filter
  Workflow.scala      render, check, context, status, snapshot
  Git.scala           the code a decision saw, diffs since, the ledger's history
  Json.scala          JSON, without dependencies
  Cli.scala           the command line
examples/auth/        access control, with a plain implementation
examples/crm/         multi-tenant CRM, proven down to its implementation
tools/                the browser server and UI, the MCP server, the ledger merge driver
bin/frflow            runs them
.claude/skills/frflow the agent skill
```
