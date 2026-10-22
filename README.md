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

The developer writes the idea in `IDEA.md`. The knowledge is a **tree** of
Scala values; Lean, generated from them, proves each step:

| Kind | Written as | Proven |
|---|---|---|
| root | `Node.root[M](id, statement, why, idea = "Section")(spec)` | it is the statement of one concern of the idea |
| refine | `parent.refine[M2](id, statement, why)(abs, spec)` | `spec m → parent.spec (abs m)` |
| instantiate | `parent.instantiate[M2](id, statement, why)(T := of[X], p := ...)` | the parent's results, with its open terms fixed |
| contract | `parent.contract[A, B, R](id, statement, why)(post).examples(...)(...)` | every function meeting `post` meets the parent |
| implementation | `kb.implementProven(contract)(define {...})`, or `kb.implement(contract)(plain Scala)` | a `define`: every result meets the contract, and the root holds of it (`root_impl`); plain Scala: examples and run-time checks |
| invariant | `Node.invariant[A, B](id, statement, why)(rule)`; each contract `.keeps(inv)(view)` or `.exempt(inv, because)`; each design node `.exempt(inv, because)` | every pair a call shows the rule (`view`) meets it, from the contract's post |
| design | `parent.design(id, statement, why)(files*)` | nothing: an architecture decision or a convention, decided and tracked |

So for a node, its **root theorem** holds: the root's statement is true of
every model of the node, through every link above it. With a proven
implementation, it is true of the code.

| What is recorded | Where |
|---|---|
| the idea, by concern (`## ` sections), and what it leaves out (`## Not modelled`) | `IDEA.md` |
| what each open term means in the world | `Opaque("User", "a person who uses the system")`, `Param(..., means)` |
| per node: statement, `why`, formal model, examples | the Scala source |
| per contract: what it does *not* promise, found mechanically | shown with the node |
| per node: who decided it, their reason, the alternatives rejected | `.frflow/ledger.json`, append-only |

## Who decides

**The developer decides every choice, in the browser.** The agent proposes
nodes, each with its reason and examples; the developer chooses one, with a
reason of their own, and the ledger keeps both and the rejected alternatives.
The tree is decided from the root down.

**The agent settles only what Lean proves again** (`settle`):
- a refinement or contract whose link Lean proves, with no proposal beside it,
  no new term and no invariant to keep;
- a review where only something above it moved, and Lean proves the link again;
- a new proven implementation (a `define` Lean proves to meet the contract).

Roots, instantiations (what the terms mean), designs, invariants and how a
contract keeps one, nodes out of Lean, nodes the developer once rejected or
that say what a rejected node said, plain code (examples check it, nothing
proves it), and any other change to what a node says are the developer's. **What the agent settles
is `settled`, not `accepted`, until the developer endorses it:** what rests on
it may go on, the browser shows what changed since the developer's own last
decision (content and code), and `status` fails until then.

## Drift

**One rule: a decision binds a person's reason to the hash of what they saw;
whatever moves under it puts the node back up for review.** A node under
review says why:

| Cause | What moved | Shown as |
|---|---|---|
| `self` | the node: statement, `why`, sources, examples, the terms it introduces, the definitions and types it uses, the invariants it keeps, its implementation's source; for a root, its section of the idea | a word diff against what was decided |
| `above` | the *meaning* of an ancestor, or of an invariant it keeps (rewording a `why` or adding an example does not cascade) | the diff of what moved |
| `code` | the files it governs: a plain implementation's, a design node's, anything `.governing` names | a git diff since the developer's last decision |
| `revisit` | the developer said a change above may affect it | their reason |
| `merged` | two branches decided it, and the merge kept both | both decisions |

A node removed from the model is listed as **gone** until the developer agrees.

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

**Decisions are the developer's, and show it.** The browser server signs each
decision with the developer's key, kept outside the repository
(`~/.config/frflow/signing.key`, or `FRFLOW_KEY`); its public key is committed in
`.frflow/keys/`. Once a project has a key, a developer decision without a valid
signature (one an agent wrote into the ledger) is a warning, listed in the
browser to decide again, or to sign if it is the developer's. The server takes
decisions only from the page opened from the link it printed (a session token).

## What Lean proves, and how it is kept honest

- **Links:** each formal node implies its parent; instantiation applies the
  generic theorem. Each obligation is stated by the generator, never by the
  agent.
- **Invariants:** the rule is stated once, over pairs (a reader and a record
  returned to them). Every contract in the invariant's `scope` (all, by
  default) keeps it, listing the pairs a call shows (`result.map(r => (user,
  r))`), or is exempt with a reason; Lean proves the rule for every pair from
  the post. A view whose pairs meet the rule whatever the call returns keeps
  it in name only, and fails.
- **Implementations** written as a `define` are proven to meet their contract,
  and `root_impl` composes that with the chain: the root holds of the code.
- **State.** A root over a step function `(State, Event) => State` whose spec
  is `inv(initial) && forall((s, e) => inv(s) ==> inv(step(s, e)))` states an
  inductive invariant; `FrFlow.always` lifts it to every state reached from
  `initial`. The CRM's writes are modelled this way, proven down to the code.
- **Authored link proofs need a witness:** `feasible` (some model meets the
  node), unless a proven implementation is one, so a hand-written proof cannot
  rest on a contradiction.
- **Saying nothing fails, when `frflow_auto` shows it:** a claim (a link, a kept
  invariant) that holds without the node's own statement, a node no model
  meets, and a node that makes the root hold by itself (through an `abs` or a
  substitution above).
- **Authored proofs** (`lean/Proofs/<KB>/<NODE>.lean`) state exactly the
  generated obligation, use only a few commands, are replayed through the Lean
  kernel, and have their axioms audited (every proven theorem's own audit is
  required; `sorry` anywhere fails it). Lemmas they share go in
  `lean/Proofs/<KB>/Lemmas.lean`, under the same rules.
- **Assumptions about the world are shown:** a top-level condition of a spec
  that never mentions the model.

Lean is the default. A node can opt out with `formal = false`, where a proof
costs more than it gives or the translated subset cannot say it: its model
stays Scala, its examples and `service` still run, and its link is decided by
reading. Everything below it is out of Lean too.

## Checked by running

- **Examples** run against the contract and the implementation; an
  implementation that always returns one value must fail one of them.
- **Every combination of the examples' inputs** runs through the
  implementation, against the contract and its invariants.
- **In production,** `service` checks every result against the contract and
  its invariants, and refuses to start if a parameter it reads is not bound.

## Status, for CI

`status` exits 1 unless every node is accepted by the developer (nothing the
agent settled waits for endorsement), every formal link, invariant and proven
implementation is proven, every example passes, and there is no warning:
- a committed version of the ledger, or the ledger now, changed or removed
  decisions of a version it follows (compared with every parent of a merge);
  a commit that does so (a revert, a deleted ledger) is a warning until the
  developer acknowledges it, with a reason;
- a developer decision not signed by a key in `.frflow/keys` (once there is one);
- a file governed by two nodes;
- a file under `src/main` governed by no node, or code in the model's file
  that is not the model;
- a section of the idea no root is decided against, when roots name sections;
- a contract that never reads a parameter its ancestors use, or a statement
  naming a rejected node;
- `.frflow/checks.json` committed (proof results come from running `check`,
  so CI runs `check` before `status`).

Structural problems (two parameters with one name, a contract or design node
in an invariant's scope that neither keeps it nor is exempt, a view that
chooses by a condition) stop the CLI. Proof results are local: CI starts from
a clean checkout and runs `check` before `status`.

## Large projects, built by agents

- **The theory lives in files.** Each agent reads the slice it needs with
  `context(node)`: the path from the root with every reason and rejected
  alternative, the invariants that apply, what moved, and the decisions below.
- **Before adding, find.** `find` names the nodes that govern a file or
  mention a concern, so an agent extends the theory instead of forking it.
- **Every file has one owner**, or `status` fails. The model itself may span
  several files (one per concern, say); each holds only the model.
- **Cross-cutting rules are stated once**, and a new contract or design node
  cannot skip one silently: it keeps it or says why not.
- **Concerns are separate.** Each root names its section of `IDEA.md`; editing
  one section reviews only its root.
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

val knowledge = KnowledgeBase("Crm", idea = "IDEA.md")(isolation, readApi, accounts, readContract, readSideWiring, noCrossTenantRead)
  .implementProven(readContract)(search)
```

Lean proves `ReadApi` implies the root, `ReadContract` implies `ReadApi` under
the CRM's meanings, that every record it returns keeps `NoCrossTenantRead`,
and that `search` meets `ReadContract`: tenant isolation holds of the code.
Production reads through `knowledge.service(readContract)(...)`, in a file the
design node `ReadSideWiring` governs.

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

The browser shows the tree (green links are proven), each node with its
examples, its link side by side with its parent, its invariants, and **the
decision**: choose between proposals, or see what moved and accept it. The
inbox lists what waits for the developer, and what the agent settled. The idea
is edited there too; saving it starts a render.

The MCP tools are `inbox`, `context`, `render`, `check`, `answer`, `settle`,
`find` and `scaffold`. None chooses. The skill
(`.claude/skills/frflow/SKILL.md`) gives the agent its loop.

## What is proven, checked, and trusted

- **Proven by Lean:** every formal link, kept invariant and `define`
  implementation, so every formal node's root theorem. The levels are
  consistent with each other; it does not say they are the right theory.
- **Checked by the examples:** that a contract means what its statement says,
  and that the implementation does what was decided, in those cases.
- **Enforced at run time:** every result of `service` meets the contract and
  its invariants, or `ContractViolation` is raised.
- **Decided by the developer:** every node, with its reasons.
- **Trusted:**
  - the Scala-to-Lean translation (it refuses what it cannot translate
    faithfully: shadowed names, names Lean's prelude defines (renamed),
    matching on `true`/`false`, type tests, function-typed fields, types that
    redefine equality, arithmetic on `Int`/`Long` (which wraps in Scala: use
    `BigInt`), division by anything but a literal);
  - parameters bound to the data the vocabulary says they mean;
  - that `abs` describes what the system does with the model;
  - every path to the data goes through `service` (the wiring is in a file a
    design node governs, and every change to it is the developer's);
  - the developer's signing key, which the agent must not be able to read (the
    browser runs on the developer's machine; agents run in their sandbox);
  - authored proof files, which Lean runs when checking (the filter is hygiene;
    the guarantee is the kernel replay and the axiom audit).
- **Not covered:** properties over time or state, effects outside a pure core
  behind `service`, whether a contract can be met beyond its examples (a
  proven implementation shows it can), and code outside `src/main`.

## Usage

Requirements: JDK 17+, sbt, and Lean 4.35.0 (`lake` on the PATH, or `FRFLOW_LAKE`).

```sh
sbt test                                  # unit tests, and Lean tests when lake is available
sbt "crm/run render"                      # Lean and the snapshot .frflow/kb.json
sbt "crm/run check"                       # prove the changed links, record the results
sbt "crm/run status"                      # exits 1 unless everything is decided, proven and passing (CI)
sbt "crm/run context ReadContract"        # everything known about a node, for agents and people
```

Committed: the Scala, `IDEA.md`, `.frflow/ledger.json` and `lean/Proofs`.
Everything else is derived and git-ignored.

## Layout

```
lean/FrFlow/          the Lean side: the frflow_auto tactic
core/                 the Scala library
  Model.scala         Opaque, Param, define
  Lift.scala          the macro: Scala lambdas to Lean
  Node.scala          nodes, invariants, examples, the knowledge base, service
  Decisions.scala     decision states and rules, shared by the CLI, browser and MCP
  Ledger.scala        the decision record, and its merge
  Generate.scala      Lean generation
  Workflow.scala      render, check, context, status, snapshot
  Git.scala           the code a decision saw, diffs since, the ledger's history
examples/auth/        access control, with a plain implementation
examples/crm/         multi-tenant CRM, proven down to its implementation
tools/                the browser server and UI, the MCP server, the ledger merge driver
bin/frflow            runs them
.claude/skills/frflow the agent skill
```
