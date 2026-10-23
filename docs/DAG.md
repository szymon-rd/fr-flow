# FrFlow on a DAG of refinements: the design

This file is the contract every change follows. Where code and this file disagree, this file wins; a
change that needs to depart from it says so in its commit message and in this file.

## 0. Principles

1. **One root.** A knowledge base has exactly one root: the idea's purpose, in one sentence, stated
   as *exactly* (what users can do and what must never happen, together), so that a system that does
   nothing does not meet it.
2. **A tree of refinements, as a DAG.** Every other node refines the nodes above it, and may refine
   several. Every edge is proven and every node is decided: a knowledge base of why the system is as
   it is.
3. **Granular and understandable.** One node says one thing, in the developer's domain words, in one
   sentence. A node that only restates its parent is not a node. A formula that packs several
   independent properties is split into parts. A parent should have 2 to 5 parts.
4. **Domain-driven.** The root speaks in the most general terms (users, applications, access); nodes
   below introduce the domain's concepts (realm, session, token) by decided definitions, as they are
   needed. Each term has one meaning, written in words (`means`), and at most one definition in force.
5. **Proofs are central.** Every edge is a Lean theorem; the code at the leaves is proven against its
   contract where it is a `define`; what is trusted is a named, visible list.

## 1. Vocabulary

- `Opaque("Realm", means)`: a domain type, open until a definition fixes it.
- `Param[T]("sessions", means)`: a domain term of type `T`, open until a definition fixes it. It is a
  fact of the world (`enabled`), or an **operation** of the system (`introspect`): a term some
  contract or assumption is about (`op`), which code implements.
- `define { ... }`: a named function, translated to Lean and run as Scala.

An open term is a Lean binder: what is proven holds for every value of it. Every term is open or has
exactly one definition in force. The vocabulary is in modules of its own, so a change to one term
rebuilds only the nodes that use it: `FrFlowGen/<KB>/Types.lean` holds the domain types and each type
in force as an `abbrev`; each `define` and each defined term has a module, `Domain/Def_<name>.lean`
and `Domain/Term_<name>.lean`, a term as a `def`; `Domain.lean` only imports them all. A node's
own declarations (`claim`, `post`, `rule`) take every term they mention as a binder; its statements
(`complete`, `holds`, the tries, `impl`, `root_impl`) apply them to the definitions in force. So a
node's Lean does not change when a term it uses gets a definition; only its statements do. A defined
term's Scala value is evaluated where it is used, under the bindings in force.

A `Param` of an opaque type cannot be applied, in Scala, to the concrete type a definition fixes:
parts below a type's definition are written in concrete terms, and definitions relate the general
terms to them (`examples/auth`).

## 2. Nodes

Kinds (JSON `kind`): `claim`, `contract`, `assumption`, `definition`, `design`. An invariant is a claim
with a `rule`.

| Kind | Scala | Lean |
|---|---|---|
| claim | `Node.claim(id, statement, why, idea = "")(formula)` | `def claim : Prop` over its open terms |
| root | the claim with no parents | as a claim, plus `idle` |
| invariant | `Node.invariant[A, B](id, statement, why, scope)(rule)` | a claim whose parts are its keepers |
| contract | `Node.contract(op)(id, statement, why)(post)`, `op: Param[(A, B) => R]` | `∀ a b, post(a, b, op(a, b))`; `impl` when a `define` is attached |
| assumption | `Node.assumption(op)(id, statement, why)(post)`, or `Node.assumption(id, statement, why)(formula)` | a hypothesis of `root_impl`: trusted |
| definition | `Node.definition(id, statement, why)(Opaque := of[T], param := expr, ...)` | an `abbrev` in `Types.lean`, a `def` in its term's module |
| design | `Node.design(id, statement, why)(files*)` | none: it governs code no proof covers |

Edges:

- `.under(parents*)` on a claim, contract, assumption or design node: this node is a **part** of each
  parent. Edges point up: adding a part never edits the parent's file. A design node under a node is
  not a part of what it says.
- `.replaces(other)`: an **alternative**. Accepting one rejects the other. Two definitions of one term
  are alternatives without `replaces`; until one is chosen, the nodes using the term are `waiting`,
  and examples and `service` use the first listed.
- A definition has no parents. It is used by every node whose statements mention a term it defines
  (directly or through other definitions).
- A contract keeps an invariant with `.keeps(inv)(view)`, which makes it a part of the invariant: the
  invariant's formula is the conjunction, over its keepers, of `∀ a b, ∀ p ∈ view(a, b, op(a, b)),
  rule(p)`. Every contract in the invariant's scope keeps it or is `.exempt` with a reason; so is every
  design node in the scope.

Structure rules (`KnowledgeBase.problems`): exactly one claim without parents; no cycles; an
assumption or a contract has no parents only when code calls its operation; a design node has a
parent; a definition has none; at most one definition in force per term.

Also part of the DSL: `examples(bindings*)(expect/reject...)`, `checkedBy`, `implement`,
`implementProven(contract)(define)` and `(define, runs)`, `service`, `expects`, `forall`/`exists`.

`IDEA.md`: the title and lead paragraph are the root's. Any node may name a section with
`idea = "Section"`; a section no node names is a warning.

## 3. Lean obligations

For each node N with parts C1..Cn (n ≥ 1), over the union U of the open terms the statements mention:

| Name | Statement | Proven by | Failing means |
|---|---|---|---|
| `complete` | `∀ U, C1 → … → Cn → N` | matching, `frflow_auto`, or `theorem complete` in `lean/Proofs/<KB>/<N>.lean` | the parts do not make N: open |
| `needed_C` (n ≥ 2) | tried: `∀ U, (∧ the other parts) → N` | `frflow_auto`, 4000 heartbeats | proven: C is not needed for N; the split is unproven |
| `vacuous` (n = 1) | tried: `∀ U, N` | as above | proven: N says nothing its part adds; unproven |
| `restates` (n = 1) | tried: `∀ U, N → C1` | as above | proven (with `complete`): N says what its part says; `status` warns of it |
| `clash` | tried: `∀ U, C1 → … → Cn → False` | as above | proven: the parts contradict each other; failed |
| `unsat` (every claim) | tried: `∀ U, ¬ N` | as above | proven: no world meets N; failed |
| `feasible` | `∃ U, C1 ∧ … ∧ Cn` | in the proof file | asked only of an authored `complete` on a node nothing witnesses |
| `idle` (root only) | tried: the root with every operation doing nothing (`[]`, `none`, `False`, its input unchanged) | Lean's default budget | proven: doing nothing meets the purpose; unproven |
| `impl` | `∀ U, promises of the callees → claim[op := code]` | `frflow_auto` or authored | the `define` does not meet the contract |
| `check` | post → the `checkedBy` check | as above | the cheap check does not follow |
| `cover_X`, `expect_i` | the view lists every value the rule is about; the expectation follows from N | as above | |
| `eval_i`, `probe_j` | an example, or an input near one, evaluated as Scala computes it | `frflow_eval` | Lean and Scala disagree: the translation is wrong |

A try is one-sided: `shown` means Lean proved it; `not-shown` means it found no proof within its
budget, and its detail says so ("Lean found no proof that N holds without it (a try)"). Never read a
`not-shown` try as a proof that a part is needed. `unsat` is the guard for a node no `feasible` is
asked of: a contradictory node would make everything above it provable.

A node is witnessed when it has proven code, is an assumption, or all its parts are witnessed. The
assumptions' joint consistency is trusted.

Composition: each node gets `theorem holds : ∀ U, Leaves → N` (the contracts, assumptions and
part-less claims below N), built from the `complete` theorems in topological order; a shared node is
proven once. The knowledge base gets `theorem root_impl : ∀ U', Assumptions → Root[op := code for
every op with a proven define]`. Its hypotheses are the trusted base, shown by `status`. `impl` is
proven from the promises of the operations the code calls, never from their code.

Lean modules per node: `Spec` (the claim and statements), `Auto` (`complete`; empty when the proof
file proves it), `Theorems` (`holds`), `Impl`, `Checks` (the tries, `check`, `cover_X`, `expect_i`,
`feasible`) and `Eval`; then `RootImpl.lean`. Before them, the vocabulary's: `Types`, a `Def_` or
`Term_` module per `define` and defined term, and `Domain`, which imports them. Each `Def_`, `Term_`
and `Spec` ends with `frflow_match_eqns`, so a `match`'s equations are made where it is declared and
not again in two modules a third imports.

Library (`lean/FrFlow/`): `frflow_auto`, `frflow_intro` (binders by their generated names, `h_<Part>`
for each part), `FrFlow.always`, `simulates`, `tracks` and `tracks_eq`, `run_snoc`, and list lemmas.

A node's check hash covers its own Lean, and its parts' statements (`holds`), not their proofs or
code; the root's covers everything (`root_impl`). A node is checked again when the hash moves, when a
part stops being proven, or when the checker's version changes.

## 4. Snapshot (`.frflow/kb.json`), per node

- `kind`, `parents`, `parts` (in the model's order), `replaces`, `op`, `rule` (an invariant).
- `defines` (a definition's terms); `uses` (the definitions in force it depends on); `relies` (the
  contracts its code calls).
- `split`: `{complete, needed: [{id, status, detail}], clash}`. `complete` is `proven`, `open`,
  `failed`, `unchecked` or `timeout`; a try is `shown` or `not-shown` (with one part, `needed` holds
  `vacuous`).
- `status`: the check of its statement (`proven`, `open`, `failed`, `model-error`, `waiting`,
  `timeout`, `unchecked`); none for definitions and design nodes. `waiting`: proven itself, but a part
  is not yet, or a term it uses has two definitions and neither is chosen.
- `leaf` (a claim nothing below proves), `idle` (on the root, what doing nothing is when Lean shows it
  meets the root), `rootImpl`, `obligations` (each with its statement), `holds`, `examples`,
  `invariants`, `expectations`, `implementationProof`.
- `content`: what the developer decides. A statement's content carries `parts`; definitions and design
  nodes have none.
- Top level: `root`, `definitions`, `trusted` (the hypotheses of `root_impl`), the vocabulary.

## 5. Decisions

- A node is decided once, whatever the number of its parents. Its decided content includes its
  statement, formula and `why`, and for a node with parts, the list of its parts.
- **Causes.** `self`: its content changed, without `parts` and `parents`, and with the `.under(...)`
  calls taken out of its source (a design node keeps `parents`). `parts`: the set of its parts changed.
  `above`: its `parentChain` changed, that is the meaning of its parents, of the definitions it uses
  and of the contracts its code calls, each with its own chain. A node's meaning has no `parts`, so a
  new sibling reviews the parent only, and a change above a diamond moves the shared node once. Also
  `code`, `revisit`, `merged` (two decisions following the same one: two branches).
- **Review follows meaning.** Rewording a formal node, with what Lean reads unchanged, reviews that
  node (`self`) and not what rests on it: its chain is read with the reworded node as it was decided.
  Its review lists the decisions below it, to revisit by name. Any change of a formula cascades.
- **Accepting** a node whose own content did not change is recorded as a `confirm`: the reason it was
  chosen stays. A node is confirmed only once all it rests on is accepted, parents first. Accepting a
  change acts on `below`: everything that rests on it, however far down (parts, users of a
  definition, callers of a contract, keepers of an invariant), each once, parents first. Those named
  with `--revisit` are revisited; those that moved only with it are confirmed.
- **Mechanical**: a node under review, not a definition or a design node, whose causes are among
  `self`, `above` and `parts`, whose own content did not change, that Lean proves again with its
  examples passing; under `parts`, with `complete` proven, no part shown not needed and no clash
  shown. The mechanical batch is one decision (`confirm`).
- **Order.** A proposal, or a node whose `above` moved, waits for the first of its parents, then the
  definitions it uses and the contracts its code calls, that is not accepted (`waitsFor`).
- **Alternatives** are `replaces` and two definitions of one term; siblings are parts, not
  alternatives. The annotated snapshot gives each node its `rivals`; accepting one rejects them.
- **Refused**: a decision on a node that moved since the developer saw it (`seen`), a reason of fewer
  than a few words, a rejection of a node that is not a proposal.
- **The ledger** holds, per node, its decisions in order. Each records the content and chain it was
  bound to, the reason, the alternatives rejected, the commit (code diffs run against it), the
  decision it follows, and the developer's signature. A decision not signed by a key in
  `.frflow/keys/` is a warning.
- **Requests.** The developer asks for a change on a node or on the idea; a request records the
  version of the node asked about. The node is with the agent until the agent answers or the node
  changes, and is not in the developer's queue meanwhile.

## 6. Agents

`context NODE` (`show --full`) gives what bears on a node: its idea section, the vocabulary it uses
with the definitions in force, its ancestors with their reasons, its co-parts under each parent, its
parts, the rejected alternatives and why, what moved, and its obligations in Lean. `find` searches
nodes, reasons, rejected options, gone nodes, the idea and Not modelled, and names the nodes that
govern a file. A new statement belongs under the lowest nodes it helps prove, as a part; never as a
restatement. A rejection's reason that asks for something is answered by a node in its place.
`scaffold` writes proof stubs that start with `unfold Obl.X`, `frflow_intro` and
`simp only [frflow_defs] at *`; `check` prints the goal they leave when automation gives up.

The developer's flow and the agent's are in the CLI. The web view and the MCP server are on the
branch `web-view`, which will become a separate repository.
