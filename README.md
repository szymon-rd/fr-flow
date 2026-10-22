# FrFlow

FrFlow builds a system as a chain of proven logical refinements, from the idea
down to the code. A person decides every step, and every drift from those
decisions is shown. The aim is to keep the theory of the system and stop
drift, also when agents build most of a large project.

## Problem

Agents add logic step by step, with no stated relation to the intent, so
correctness and design coherence cannot be tracked. A program is the visible
part of a theory its programmers hold (Naur, 1985): why it is as it is, and
how it maps to the world. With agents, the developer often never builds that
theory, and the agent loses it when its context is compressed. A large system
needs its theory to outlive every context window.

## The method

The developer writes the idea in `IDEA.md`, one `## ` section per concern. An
agent writes Scala nodes: a tree under each root, and invariants across the
trees. Lean, generated from the Scala, proves each link.

| Kind | Written as | Lean proves |
|---|---|---|
| root | `Node.root[M](id, statement, why, idea = "Section")(spec)` | nothing: it states one concern of the idea |
| refine | `parent.refine[M2](id, statement, why)(abs, spec)` | `spec m → parent.spec (abs m)` |
| instantiate | `parent.instantiate[M2](id, statement, why)(T := of[X], p := ...)` | the link holds by substitution; Lean checks it builds |
| contract | `parent.contract[A, B, R](id, statement, why)(post)`, or `contractVia(...)(abs)(post)` | every function meeting `post` meets the parent |
| implementation | `kb.implementProven(contract)(define {...})`, optionally `(define {...}, fastCode)`, or `kb.implement(contract)(plain Scala)` | a `define` meets the contract, and the root holds of it (`root_impl`); `fastCode` runs, checked to return what the define does |
| invariant | `Node.invariant[A, B](id, statement, why)(rule)`, kept with `.keeps` or `.exempt` | every pair a keeping contract shows meets the rule |
| design | `parent.design(id, statement, why)(files*)` | nothing: an architecture choice or convention, decided and tracked |
| expectation | `node.expects(statement)(m => ...)` | a consequence the developer expects, from the node's spec |
| reliance | `.relies(other, why)`, or `.relies(other, why, guarantee)(sees)` | the guarantee, of every state `other`'s concern reaches |
| call | `val c = contract.caller("c")`, called in a `define` | the calling code, from the callee's contract alone |

So for each formal node, the root's statement is true of every model of the
node, through every link above it. With a proven implementation, it is true of
the code.

`IDEA.md` holds the idea and what it leaves out (`## Not modelled`, with a
`### ` subsection per concern if needed). The Scala holds each node's
statement, `why`, model and examples, and what each open term means
(`Opaque`, `Param`). `.frflow/ledger.json` holds each decision: who, their
reason, the alternatives rejected, signed; it is append-only.

## Who decides

The developer decides every node, in the browser, from the root down. The
agent proposes nodes, often alternatives as siblings, each with its reason and
examples; the developer chooses one, with a reason of their own. The agent
works through MCP and the CLI, and no tool of the agent's decides.

**Mechanical decisions.** One rule (`Decisions.mechanical`): a node under
review (never a proposal), not a root or a design node, where nothing the
developer decided changed (only the types it uses, a proven implementation, how
its examples print, or something above it moved), and Lean proves it again. An
instantiation's choice is what it substitutes, which is part of what it says. The browser offers them as one batch, accepted
with one reason.

**Signing.** The browser server signs each decision with the developer's key,
kept outside the repository (`~/.config/frflow/signing.key`, or `FRFLOW_KEY`).
Every public key in `.frflow/keys/` is a developer key. A decision not signed
by one is a warning, so `status` fails; the browser lists it, to decide again
or sign. Decisions with no key at all are a warning too: start `frflow serve`
(it creates the key) and commit `.frflow/keys/`.

## Drift

One rule: a decision binds a person's reason to the hash of what they saw.
Whatever moves under it puts the node back up for review, with the cause:

| Cause | What moved | Shown as |
|---|---|---|
| `self` | the node: its definition as written, statement, `why`, examples, terms, the definitions and types it uses, kept invariants, implementation source; for a root, its section of the idea | a word diff |
| `above` | the meaning of an ancestor, of a kept invariant, or of a node it relies on | the diff of what moved |
| `code` | the files it governs: a plain implementation, a design node's files, `.governing` paths | a git diff since the decision |
| `revisit` | the developer said a change above may affect it | their reason |
| `merged` | two branches decided it, and the merge kept both | both decisions |

Rewording a `why` or adding an example does not cascade below. A change that
does not cascade may still break a reason written below. So accepting a change
lists the decisions below, each with the reason it holds by now; the developer
marks those it may affect (`revisit`), and confirms by name those that moved
only because of it. A decision whose reason or `why` says when it stops
holding ("revisit if", "reconsider when", "unless", "until", "as long as",
"only while") must be answered by name: still holds, or revisit. So must such
a decision above a new node (on its path, what it relies on, what it keeps):
the new node may be what the condition was about.

A decision is refused if the node or its code moved since the developer looked
at it, or if its reason is not a few words. A review can be sent back to the
agent as a request. A decided node removed from the model is listed as gone
until the developer agrees. When a new proposal says the same (ids and the
val's name aside), the browser offers "Renamed to X": one decision that keeps
the history, reasons and rejected alternatives.

## What Lean proves

- **Links.** Each formal node implies its parent. The generator states each
  obligation; the agent never does.
- **Invariants.** A rule is stated once, over pairs (a reader, a record shown
  to them). Every contract in its scope keeps it, listing the pairs a call
  shows, or says why it is exempt; so does each design node in the scope. Lean
  proves the rule of every listed pair (`inv_X`), and, for a rule about a
  domain or opaque type, that the view lists every such value (`cover_X`).
- **Implementations** written as a `define` meet their contract, and
  `root_impl` composes that with the chain: the root holds of the code.
- **Examples, both ways.** Lean evaluates each example of a formal contract
  whose parameters are values (or `bindTable` lookups): it must prove what
  Scala computes and not its opposite, or the node fails. A formal contract
  with no example Lean evaluates is a warning.
- **State.** A root over runs (`List[Event] => State`) is refined by a step
  `(State, Event) => State`; the link is proven by induction (`FrFlow.always`).
- **Composition.** Code calls another contract through `contract.caller`: Lean
  proves it assuming only the callee's `post`, so each contract is proven once
  and a caller does not depend on the callee's code. Only a callee with proven
  code is assumed (its code shows the promise can be kept), and the callee's
  parameters the caller does not read are bound once, beside the caller's (one
  store for every call). Examples and `service` run the callee's registered
  code for the call. The caller rests on the callee: a change to the callee's
  meaning reviews it. `DealSearch` in `examples/crm` is built on `ReadContract`.
- **Seams.** In `.relies(other, why, guarantee)(sees)`, Lean proves
  `guarantee` of every state `other`'s concern reaches (`rely_<Other>`); at
  run time it is checked on what `sees` returns.
- **Authored proofs** (`lean/Proofs/<KB>/<Id>.lean`, shared lemmas in
  `Lemmas.lean`) state exactly the generated obligation, use a few allowed
  commands and imports, and have their axioms audited (`sorry` fails). A
  hand-proven link also needs a witness: `feasible` (some model meets the node)
  or a proven implementation below it, and `nontrivial` (some model fails the
  root). So a proof cannot rest on a contradiction or a vacuous root.

**Saying nothing** is caught where `frflow_auto` can prove it:

| Check | Catches | Result |
|---|---|---|
| `vacuous_<claim>` | a link, kept invariant or expectation that holds without the node's own statement | the claim fails |
| `unsat` | a refinement or contract no model meets | the link fails |
| `rootTrivial` | a root that holds of every model, by an `abs` or substitution above | the link fails |
| `idle` | doing nothing meets the contract | shown as a limit |

Lean is the default. Where the Lean subset cannot say a node, or a proof costs
more than it gives, the node opts out with `formal = false`: its model stays
Scala, its examples and `service` still run, its link is decided by reading,
and everything below it is out of Lean too.

**Checked by running.** Examples run against the contract and the
implementation, and the implementation also runs on every combination of the
examples' inputs. In production, `service` checks every result of plain code
against the contract and its invariants (proven code is not checked again), and
the guarantees relied on whenever a value it reads changes, or raises
`ContractViolation`; it refuses to start if a parameter it reads is unbound.

## Status and CI

`status` exits 1 unless every node is accepted, nothing is left unproven (one
list per node, `Decisions.unproven`: link, examples, invariants, proven
implementation, expectations, guarantees relied on), no node is gone, and
there is no warning. Warnings: a decision not signed by a developer key, or
decisions with no key; a file governed by two nodes, or by none (any source in
the project but tests, build output, `lean` and `.frflow`); a section of the
idea no root names; a statement or `why` naming a rejected or removed node; a
formal contract with no example evaluated in Lean.

`ci` is what CI runs: `check` (a node whose formal parts did not change keeps
its result), then `status`.

## Large projects

The theory lives in files, not in an agent's context: `context(node)` gives
what bears on a node (idea section, vocabulary, path with reasons, rejected
alternatives, reliances, what moved), and `find` searches nodes, reasons,
rejected options and the idea, so an agent extends the theory instead of
forking it. Every file has one owner, cross-cutting rules are stated once, and
editing one section of the idea reviews only its root. Use one model file per
concern (the Scala compiler fails at about 30 nodes in one file). `check` runs
nodes side by side in levels (`FRFLOW_THREADS`); a Lean timeout gives status
`timeout` and is checked again. The ledger only grows; enable its merge driver
once per clone; a node both branches decided is decided again:

```sh
git config merge.frflow-ledger.driver "bin/frflow merge-ledger %O %A %B"
```

**Measured.** `python3 bench/generate.py N` writes `examples/scale`: N concerns,
each a root, a refinement and a contract with proven code in its own file,
every fifth contract calling the previous one's (`sbt "scale/run check"`). On
a 4-core container:

| nodes | cold `check` | one code change | no change | `status` | browser load |
|---|---|---|---|---|---|
| 60 | 193 s | 21 s | 6 s | 5 s | |
| 180 | 560 s | 18 s | 5 s | 5 s | 0.35 s |

A cold check grows with the nodes (about 3 s each); after that, only what a
change reaches is proven again (a root change: its concern and the callers of
its contract).

## What is trusted, and the limits

Lean proves the levels consistent with each other; it does not say they are
the right theory. That is the developer's decision. Trusted:

- the Scala-to-Lean translation, cross-checked only on the examples; it
  refuses what it cannot translate faithfully (`Int` arithmetic, for one);
- that parameters hold the data they are said to mean, and that `abs`
  describes what the system does;
- that every path to the data goes through `service`, and that what `sees`
  returns is a state the relied concern reached (the governed wiring);
- the signing key, which the agent must not be able to read: run the browser
  server outside the repository the agent edits;
- the model's program. FrFlow runs it to read it, so the gate stops drift, not
  an agent that writes code to subvert FrFlow. Every node's definition as
  written is decided, and every source file has a reviewed owner.

Limits: the "says nothing" checks are one-sided; examples with function-valued
parameters (other than `bindTable`) are not evaluated in Lean; running covers
the examples and their combinations, not every input; an `idle` contract
promises nothing beyond its examples; ordering, liveness and effects outside a
pure core behind `service` are not covered. Maps and sets are functions in
Lean: what needs iterating them (sizes, all keys) cannot be said, and an example
whose maps differ at a key it does not name may be left unevaluated.

## Example: a multi-tenant CRM (`examples/crm`)

```scala
val isolation = Node.root[(User.T, Record.T) => Boolean]("TenantIsolation",
  "A user sees a record only if it belongs to their company or was shared with their company.",
  why = "...", idea = "Reading records")(
  shows => forall((u: User.T, r: Record.T) => shows(u, r) ==> visible(u, r)))

val readContract = accounts.contract[Account, Search, List[CrmRecord]]("ReadContract", "...", why = "...")(
  (user, query, result) => result.forall(r => store.value.contains(r) && matches(query, r) && mayRead(user, r)) && ...)
  .examples(...)(expect(...), reject(...))
  .keeps(noCrossTenantRead)((user, query, result) => result.map(r => (user, r)))

val knowledge = KnowledgeBase("Crm", idea = "IDEA.md")(isolation, readApi, accounts, readContract, ...)
  .implementProven(readContract)(search)
```

`ReadApi` and `Accounts` (not shown) refine it to queries and instantiate it
with the CRM's types. Lean proves each link, that every record `ReadContract` returns keeps
`NoCrossTenantRead` (and the view lists them all), and that `search` meets
`ReadContract`: tenant isolation holds of the code. Writes are a second
concern, a state machine whose `applyWrite` is proven by a short authored
proof. `Accounts` relies on the writes for unique ids (`rely_CrmWrites`).
`examples/auth` does access control with a plain implementation; its ledger
keeps the rejected `ClientAsserted` and a reason that says when to revisit.
(The example ledgers were written by an agent, to show the method.)

## Usage

Requirements: JDK 17+, sbt, and Lean 4.35.0 (`lake` on the PATH, or
`FRFLOW_LAKE`).

```sh
bin/frflow serve examples             # the browser, where the developer decides
bin/frflow mcp examples               # the MCP server for agents (see .mcp.json)
sbt test                              # unit tests, and Lean tests when lake is available
sbt "crm/run render"                  # Lean and the snapshot .frflow/kb.json
sbt "crm/run check"                   # prove what changed, record the results
sbt "crm/run status"                  # exits 1 unless decided, proven and passing
sbt "crm/run ci"                      # what CI runs: check, then status
```

The browser shows each node with its examples (and whether Lean agrees), its
link, reasons, rejected options and what it leaves unproven; its inbox lists
what waits. The agent's rules are in
[`.claude/skills/frflow/SKILL.md`](.claude/skills/frflow/SKILL.md).

Committed: the Scala, `IDEA.md`, `.frflow/` (ledger, keys, requests) and
`lean/Proofs`; the rest is derived. What a newer FrFlow adds to a node's
content (its definition text, in format 3) is not a change: decisions recorded
before need no new decision.

## Layout

```
lean/FrFlow/            the Lean side: definitions and the frflow_auto tactic
core/                   the Scala library
  Node, Model, Lift     nodes, Opaque, Param, define; the macro from Scala to Lean
  Generate, Lean        Lean generation; running lake, axiom audits, the proof-file filter
  Decisions             decision states and rules, shared by the CLI, browser and MCP
  Ledger, Signing       the decision record and its merge; keys and signatures
  Workflow, Cli, Git    render, check, context, status; the command line; diffs
examples/auth/          access control, with a plain implementation
examples/crm/           multi-tenant CRM, proven down to its implementation
tools/                  the browser server and UI, the MCP server, the merge driver
bin/frflow              runs them
.claude/skills/frflow   the agent skill
```
