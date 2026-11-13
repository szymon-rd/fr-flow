# FrFlow on a DAG of refinements: the design

This file is the design every change follows, in brief; [redesign/ARCHITECTURE.md](redesign/ARCHITECTURE.md) is the
full record, and [redesign/owner-decisions.md](redesign/owner-decisions.md) the owner's decisions it applies (§n
below). Where code and these disagree, they win; a change that needs to depart from them says so in its commit message
and in them.

## 0. Principles

1. **A small set of roots.** A FrModel has one or a few root statements, on any of its Definitions and Declarations
   and relating them too, kept concise by its author: each states one idea, and together they are the purpose (§11).
   A root is stated as *exactly* (what users can do and what must never happen, together), so that a system that
   does nothing does not meet it; the `idle` try asks it of the roots together. Where the purpose is more general
   than the code, it is stated over Declarations, and claims at the bottom say what each is in terms of the code
   (rooms' `bookedAfterIsStored`).
2. **A graph of refinements.** Every other node refines the nodes above it, and may refine several, so the nodes form
   a directed acyclic graph. Every step is proven, every node is decided: a model of why the system is as it is.
3. **Granular and understandable.** One node says one thing, in the developer's domain words, in one sentence; no
   concepts glued with `&&` (a style guide, not a check: §10, §16). A node that only restates its part is reported
   (`restates`). A parent should have 2 to 5 parts. The first split is ⇒/⇐ (safety and capability) or state/reads,
   not one part per conjunct.
4. **Domain-driven.** The roots speak in the most general terms; nodes below introduce the domain's concepts as they
   are needed. Each value has one meaning, written in words (`means`), and is given its meaning once.
5. **Proofs are central.** Every step is a Lean theorem; the code at the leaves is proven where it is written in the
   DSL, and tested where it is plain Scala; what is trusted is a named, visible list of assumptions. Nothing is
   checked when the code runs (§2): FrFlow is for testing before production and strict static guarantees.
   A departure, on the branch that adds it: plain Scala the compiler reads (`lifted { … }`) is proven too, as the
   term read from it ([LIFTED.md](LIFTED.md) says what holds the Scala to that term). It adds no concept: lifted
   code is a Definition given its meaning on the spot, and a type's contract (`FrSpec`) is an `always[T]` a node
   states. A second departure on that branch: a method that changes a structure is read as a function of the
   structure's state, and among other calls as a function of a schedule too; what the reading takes for granted
   (a store's member is one step) is said by design nodes. A value with members (a structure: a service whole) is a word too: a Declaration of a trait's type,
   its members called in claims, the class that implements the trait its Definition; a claim on it is said of the
   structure in every state. A third:
   the two kinds of value are one. Every word is a Declaration, and a Definition is a Declaration with a meaning
   (`granted.define { … }`, listed in the FrModel beside the nodes; or `define { … }`, declared and defined at
   once). Code calls Declarations; which of them are fixed (given a meaning, or called by code) is read off the
   model. A fourth: effectful programs written in the DSL (`Flow`), state models and the clock were removed; a
   service's state is a structure's.

## 0a. The core concepts

Three kinds of nodes, two kinds of values, two quantifiers (§15); nothing else, under any name.

- **Nodes.** `Node.claim(statement)(formula)`: proven from its parts or of the code it mentions, or tested where the
  code is plain Scala. `Node.assumption(statement)(formula)`: trusted, the developer's decision: an outside system's
  promise, what values from outside meet. `Node.design(statement)(files*)`: a decision
  about code no proof covers.
- **Values.** `Declaration[A](means)`: a word, of any type, what statements speak of and code calls. A
  Definition is a Declaration with a meaning (§15): `d.define(…)` of one already declared, listed in the FrModel
  beside the nodes, or `define { … }`, declared and defined at once. A word nothing defines
  is known through the statements about it. `stated { … }`
  is a define whose body may apply a Declaration, so a statement can name a line over Declarations; only statements
  call it.
- **Quantifiers.** `forall` is every possible value, `exists` some possible value. `always` is every value the code FrFlow covers can produce
  (§19): `always[T](x => …)` every value of `T` that can be made, a hypothesis of every statement about such values
  wherever they are held, met wherever covered code makes one. Values from outside are covered by an assumption of
  `always` on their type (§21): statements are about values, not about a function's inputs.
- **Edges.** `.refines(parent)` makes a node a part, or, for a claim of `always`, a rule below the statement it
  serves (no part of the step); `.assuming(assumption)` a premise; `.replaces(other)` an alternative.

## 1. Vocabulary

- A domain type is a case class or an enum deriving `LeanType`: a Lean `structure` or `inductive`. One deriving
  `FrSpec` instead is the same, with a contract a node may state, and can be a value of lifted code.
- A word gets its meaning once: from a Definition of it listed in the FrModel (`d.define`, `d.defineTested`,
  `d.defineValue`, `d.provided`), or on the spot (`define`, `lifted`).
  `check` refuses one defined twice, and code that reaches a word only statements read.
- Names come from the `val`s: a node's id is its val's name, a Definition's and a Declaration's too. Renaming a val
  renames the node: a new node to decide (`.replaces(old)` links them).

## 1b. Proven, tested, assumed

- **Proven**: a `define`, lifted code, or a class read for a structure, of which the prover proves the claims
  mentioning it.
- **Tested**: plain Scala, tested against the claims mentioning it on generated cases (each argument drawn meeting
  the rules on its type).
- **Assumed**: what an assumption says, trusted; plain Scala an assumption is about is tested against it.

What proven code hands to plain Scala meets the rules on its type (`made_<code>_call_<i>`, §37): a proof only.

## 2. Nodes

- A claim with parts is proven from them: its parts, with the assumptions it lists, imply it (`complete`), each is
  needed (`needed_<part>`). Its rules (claims of `always` below it) are no part of the step.
- A claim mentioning proven code is proven of the code (`impl`), its parts or the claims about what the code calls
  as hypotheses. A claim at the bottom mentioning a Declaration says what the Declaration is: it is never asked
  `impl`, and the proven code stands in it in its consistency group (§3a).
- A claim mentioning plain Scala is tested against it: read as a call where it applies the Definition to exactly its
  leading `forall` variables, the whole formula evaluated otherwise; one with no Scala value is not checked, and
  `status` warns when nothing else checks it.
- An assumption is trusted, and listed by every check resting on it (`.assuming`), which FrFlow derives and checks:
  a missing premise or one not needed is refused.
- A design node governs files; a change to them brings it back. Every source file is governed by one node (an
  implementation, or a design).
- At least one root, never an assumption; no cycle over parts and premises; edges inside the model.

## 3. Lean obligations

What Lean is asked of each node is a function of the resolved theory (`proof.audit.Obligations`). Generated Lean
is under `lean/FrFlowGen/<Model>/` (a module per node, its `Spec` and its `Checks`, and the domain);
developers' proofs under `lean/Proofs/<Model>/`.

| Obligation | Asked of |
|---|---|
| `complete`, `needed_<part>` | a claim with parts |
| `impl` | a claim mentioning proven code |
| `root_impl` | the roots, of the code, through the claims saying what each Declaration is |
| `made_<maker>` | each proven define making a value an `always[T]` is about |
| `made_<code>_call_<i>` | each call from proven code to plain Scala, of the arguments' rules |
| `outside` | a claim of `always[T]` whose `T`s come from outside |
| `consistent_<i>`, `inhabited_<node>`, `satisfiable_<i>_<node>` | §3a |
| `example_<set>_<i>` | §3b |

The tries (`vacuous`, `restates`, `clash`, `unsat`, `idle`) are refuters, reported as shown or not shown. A
step refuted carries the case Lean confirms. A rule is kept only as every rule its obligations take is: a statement is
open while a rule it takes is open, for any reason (its `made_`, its tests, nothing meeting it).

## 3a. Consistency and vacuity

- **Consistency** (§15, §18, §28): the statements at the bottom and the assumptions beside them, in groups sharing an
  open value, each `consistent_<i>`: some meaning of every open value makes them all hold. Witnesses are derived where
  possible (an equation, a bound, a fixed value, proven code, solved in order); a group FrFlow cannot witness is
  proven by hand (§39). A group not proven is a failure, not a warning: the whole model's proof is red, and so is
  every statement proven from parts over a Declaration while a group below it is not proven. Tested Scala alone is
  evidence, not proof.
- **Vacuity**: positive statements guard against a model that says nothing (a root stated as *exactly*), and two
  small proofs: `inhabited_<node>`, some value meets an `always` (with every other `always` on its type), and
  `satisfiable_<i>_<node>`, each condition `A` of `A implies B` can hold. Witnesses come from the generators or a
  search of small values. Reported, not gated.

## 3b. Examples written as tests

Examples are ordinary tests (`class GrantedExamples extends FrFlowExamples(rooms)`, `example(name): fact`), read by
`check`, evaluated against the code and in Lean against the claims (`example_<set>_<i>`, the `i`th of its class). Nothing depends on them (§18): the
theory and its Lean are the same without them. An example whose values break a rule on their type is refused.

## 4. Snapshot (`.frflow/kb.json`), per node

An export for tools, in decision order; FrFlow never reads it back.

- `header`: `id`, `kind` (`claim`, `assumption`, `design`), the content as decided and its `hash`, what a decision
  binds.
- `place`: `parents`, `parts`, `assumes`, `relies` (the claims about what its code calls), `keptBy` (the programs
  keeping a rule).
- `check`: `status`, `holds`, and its `obligations`, each with its name, status and Lean's detail.
- `body`: for a claim or an assumption (`stated`), how it is checked, the call it reads as, its code and its tests
  (cases, against what, seed); for a design, the files it `governs`.
- Top level: `kb`, `roots`, `trusted` (what the roots rest on), the vocabulary (each value and what it means),
  `consistency` (each group: its statements, open and provided values, status), and the examples as checked.

A node's content is its fields as decided: `kind`, `parents`, `parts` (a claim's), `assumes`, `statement`, `formula`
(the canonical print of the elaborated formula, what a decision binds), `written` (the source, for display),
`vocabulary`, and for code `checking`, `writers`, `governs`, `call`, `replaces`, `reliance`, `failure`,
`implementation`, `model`.

## 5. Decisions

- A node is decided once, whatever the number of its parents; its decided content is its content (§4).
- **Causes.** `self`: what it says changed. `parts`: its list of parts. `above`: the meaning of what it rests on
  (its parents, the values it uses, the claims its code relies on), each with its own chain; a node's meaning has no
  parts, so a new sibling reviews the parent only, and a change above a diamond moves the shared node once. `code`:
  the code it governs. `revisit`: the developer asked. `merged`: two decisions following the same one (two
  branches).
- **Review follows meaning.** Rewording a node with what Lean reads unchanged reviews that node and not what rests
  on it. Any change of meaning cascades.
- **Accepting** a node whose own content did not change is a `confirm`: the reason it was chosen stays. Accepting a
  change acts on what rests on it, each once, parents first; those named with `--revisit` are revisited, those that
  moved only with it confirmed.
- **Mechanical**: a node under review whose own content did not change, that Lean proves again, its examples
  passing. The mechanical batch is one decision (`confirm`).
- **Order.** A node waits for the first node it rests on that is not accepted: a parent, a premise, a value it uses.
- **Alternatives** are `replaces`; accepting one rejects the other.
- **Refused**: a decision on a node that moved since the developer saw it, a reason of fewer than three words, code
  failing a generated case or not tested since it moved, a decider not listed, a ledger whose committed history was
  rewritten.
- **Who decides** (§2): `.frflow/deciders`, committed and signed by a listed key, names the keys whose decisions
  count. The ledger holds, per node, its decisions in order, each with the content it binds, the reason, the
  alternatives rejected, the commit, the decision it follows and its signature; a node's committed history must be
  a prefix of the working one, or nothing of it counts until a listed decider runs `rebase` (`.frflow/ledger-base`).
- **Held aside.** A layer on top may hold a node out of the developer's queue (while it is asked of the agent); the
  inbox lists it apart, and nothing else about it changes.

## 6. Reading a node, and where a change belongs

`show --full NODE` gives what bears on a node: its statement and formula, why it was accepted, how it is checked,
where it sits, its parts and the rules it uses, what moved, and its obligations in Lean. `find` names the nodes that
govern a file, or mention some words. A new statement belongs under the lowest nodes it helps prove, as a part; never
as a restatement. A rejection's reason that asks for something is answered by a node in its place. `scaffold` writes
proof stubs for what the last check left open; `check` prints the goal Lean leaves when automation gives up.

The developer's flow is in the CLI. The `web` module serves it in a browser (the sbt task
`sbt "PROJECT/serve --as NAME"`, not a CLI command) over the same API, so a decision is recorded alike from either.
Both take layers on top (`Extension`: a `CliExtension`'s commands and what it adds to a view; a `WebExtension`'s
routes and script); the core depends on none. The AI agent's layer is one, described in
[USAGE.md](USAGE.md#with-an-ai-agent).
