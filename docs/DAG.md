# FrFlow on a DAG of refinements: the design

This file is the contract every change in the DAG rework follows. Where code and this file disagree,
this file wins; a change that needs to depart from it says so in its commit message and in this file.

## 0. Principles (the owner's)

1. **One root.** A knowledge base has exactly one root: the idea's purpose, in one sentence, stated
   as *exactly* (what users can do and what must never happen, together), so that a system that does
   nothing does not meet it.
2. **A tree of refinements, as a DAG.** Every other node refines the nodes above it. A node may refine
   several parents. The structure is a requirement tree whose every edge is proven and whose every
   node is decided: a knowledge base of why the system is as it is.
3. **Granular and understandable.** One node says one thing, in the developer's domain words, in one
   sentence. A node that only restates its parent at a lower level of detail is not a node. A formula
   that packs several independent properties is split into parts. A parent has 2 to 5 parts; more
   asks for an intermediate concept.
4. **Domain-driven.** The model is refined by introducing the domain, step by step: the root speaks
   in the most general terms (users, applications, access); nodes below introduce the domain's
   concepts (realm, session, token) as they are needed, by decided definitions, and state properties
   in them. The vocabulary is the project's ubiquitous language: each term has one meaning, written in
   words (`means`), and at most one decided definition.
5. **Proofs are central.** Every edge is a Lean theorem; the code at the leaves is proven against its
   contract where it is a `define`; what is trusted is a named, visible list.

## 1. Vocabulary

The vocabulary is what claims talk about. It is shared by the whole knowledge base.

- `Opaque("Realm", means)`: a domain type, open until a definition fixes it.
- `Param[T]("sessions", means)`: a domain term of type `T`, open until a definition fixes it. It is a
  fact of the world (`enabled`), or an **operation** of the system (`introspect`, `step`): a function
  some contract is about and some code implements. Operations are ordinary `Param`s.
- `define { ... }`: a named function, translated to Lean and run as Scala (unchanged).

An open term is a Lean binder: what is proven holds for every value of it. A defined term is a Lean
`def` (a type: `abbrev`). Every term is open or has exactly one definition in force.

## 2. Nodes

Kinds (JSON `kind`): `claim`, `contract`, `assumption`, `definition`, `design`. Nothing else.

| Kind | Scala | Meaning | Lean |
|---|---|---|---|
| claim | `Node.claim(id, statement, why, idea = "", owner = "")(formula)` | a proposition over the vocabulary (`formula: => Boolean`, lifted) | `def claim : Prop` over its open terms |
| root | a claim with no parents | the purpose | as a claim, plus `idle` |
| contract | `Node.contract(op)(id, statement, why, owner = "")(post)` with `op: Param[(A, B) => R]` | every call of `op` meets `post`; the claim is `∀ a b, post(a, b, op(a, b))` | as a claim; `impl` when code is attached |
| assumption | `Node.assumption(op)(id, statement, why)(post)`, or `Node.assumption(id, statement, why)(formula)` | trusted, not proven: what the outside does (a port), or a fact of the world | a hypothesis of `root_impl` |
| definition | `Node.definition(id, statement, why)(Opaque := of[T], param := expr, ...)` | fixes terms of the vocabulary; decided, not proven | `abbrev`/`def`s in the vocabulary module |
| design | `Node.design(id, statement, why)(files*)` | governs code no proof covers | none |

Edges:

- `.under(parents*)` on claim, contract, assumption and design: this node is a **part** of each parent.
  A parent's parts, together, refine it. Edges point up: adding a part never edits the parent's file.
- `.replaces(other)` on any node: an **alternative** to `other`. Accepting one rejects the other (the
  rejected node is kept in the ledger with the reason, as today). Two definitions of one term are
  alternatives of each other without `replaces`.
- Definitions have no parents. A definition is used by every node whose statement mentions a term it
  defines (directly or through other definitions); that is its place in the DAG.

Structure rules (`KnowledgeBase.problems`): exactly one claim without parents (the root); no cycles;
assumptions and contracts may have no parents only when some code calls their operation; a design
node has at least one parent; every non-root claim has a parent; at most one definition in force per
term (two present: they are alternatives, decided before the nodes that use the term are checked).

Kept from today, unchanged in meaning: `examples(bindings*)(expect/reject...)`, `checkedBy`,
`implement`, `implementProven(contract)(define)` and `(define, fast)`, `service`, `expects`,
`formal = false`, `owner`, `KnowledgeBase.uses`, `Opaque`, `Param`, `define`, `forall`/`exists`.

Removed: `Node.root` (a claim with no parents), `refine` and `abs` (a part plus, where the model's
shape changes, a definition relating the terms: `shows := (u, r) => exists((q: Query) => run(u, q).contains(r))`),
`instantiate` (a definition), `contractVia`, `Node.port` (an assumption on an operation), `caller`
(code calls the operation's `Param` directly; `service` binds it to that contract's implementation),
`relies` (the relied-on fact is a shared part, or an assumption), `safety =` (the root says
*exactly*; the idle check applies to the root only), the rule that each idea section has a capability
root.

Invariants: `Node.invariant(id, statement, why)(rule: (X, Y) => Boolean)` is a claim; a contract keeps
it with `.keeps(inv)(view)` (unchanged syntax), which makes the contract a part of the invariant. The
invariant's formula is the conjunction, over its keepers, of `∀ a b, ∀ p ∈ view(a, b, op(a, b)), rule(p)`;
`cover` and `exempt` stay as today, and contracts whose result type matches the rule's and neither keep
nor are exempt stay a warning. The invariant has parents like any claim.

IDEA.md: the title and lead paragraph are the root (`idea = ""`). Any node may name a section with
`idea = "Section"`; a section no node names is a warning (as today, for any node, not only roots).

## 3. Lean obligations

For each node N with parts C1..Cn (n ≥ 1), over the union U of the open terms the statements mention:

| Name | Statement | Proven by | Failing means |
|---|---|---|---|
| `complete` | `∀ U, C1 → … → Cn → N` | `frflow_auto`, or `theorem complete` in `lean/Proofs/<KB>/<N>.lean` | the parts do not make N: open (unproven) |
| `needed_i` (n ≥ 2) | tried: `∀ U, (∧ j≠i, Cj) → N` | `frflow_auto` with a short timeout | if Lean **proves** it, part i is not needed: N's split is unproven ("Ci is not needed for N") |
| `vacuous` (n = 1) | tried: `∀ U, N` | as above | if proven, N says nothing its part adds: unproven |
| `clash` | tried: `∀ U, C1 → … → Cn → False` | as above | if proven, the parts contradict each other: failed |
| `unsat` (every claim) | tried: `∀ U, ¬ N` | as above | if proven, no world meets N: failed |
| `feasible` | `∃ U, C1 ∧ … ∧ Cn` | in the proof file | required only when `complete` is authored and no proven code witnesses the parts |
| `idle` (root only) | tried: the root with every operation replaced by doing nothing (`[]`, `none`, `False`, its input returned unchanged) | as above | if proven, doing nothing meets the purpose: unproven |
| `impl` (contract with a `define`) | `∀ U, C_callees → claim[op := code]` | `frflow_auto` or authored, as today | as today |
| `check` (`checkedBy`) | post → check | as today | as today |
| examples, probes | as today | | |

Composition: each node gets `theorem holds : ∀ U, Leaves → N` (Leaves: the contract and assumption
claims below N, and claims below N that have no parts), built mechanically from the `complete`
theorems in topological order; a node shared by several parents is proven once. The knowledge base
gets `theorem root_impl : ∀ U', Assumptions → Root[op := code for every implemented op]`, whose
hypotheses are exactly the assumptions (and any leaf claim not yet implemented). That hypothesis list
is the trusted base, shown in `status`.

Library (`lean/FrFlow/`): `FrFlow.always` (as today: a property kept by every step holds of every run)
and `FrFlow.simulates` (a step that mirrors an abstract step keeps the abstraction over every run),
used by authored proofs of state machines.

## 4. Snapshot (`.frflow/kb.json`), per node

Changed fields only; everything else stays as today.

- `kind`: one of the five kinds above.
- `parents`: list of ids (replaces `parent`). `[]` for the root, definitions, and parentless assumptions.
- `parts`: list of ids of its parts (in the model's order).
- `replaces`: id or null.
- `op`: for contracts and assumptions on an operation, the `Param` name; else null.
- `defines`: for definitions, the terms they fix; `uses`: for every node, the definitions in force it
  depends on.
- `split`: for a node with parts: `{"complete": {status, detail}, "needed": [{"id", "status", "detail"}],
  "clash": {status, detail}}` with statuses as for links today (`proven`, `open`, `failed`,
  `unchecked`, `timeout`, `informal`). Replaces `link`.
- `rule`: true for an invariant claim.
- top level: `root` (the root's id), `definitions` (ids), `trusted` (the hypotheses of `root_impl`).

## 5. Decisions

- A node is decided once, whatever the number of its parents. Its decided content includes its
  statement, formula and `why`, and **for a node with parts, the list of its parts**: adding or
  removing a part puts the parent up for review (cause `parts`). It is decided by the parent's owner.
- Causes (`causes`): `self` (its content changed), `above` (a parent's or a definition's decided
  content changed: any of them), `parts` (its list of parts changed), `code`, `revisit`, `merged`.
- Mechanical (one batch, as today): a node under review whose own meaning did not change and whose
  obligations Lean proves again; for `parts`, when `complete` is proven and every part is needed.
- A proposal waits until all its parents and the definitions it uses are accepted (`waitsFor`: the
  first that is not).
- Alternatives: `replaces`, and two definitions of one term. Siblings under one parent are parts, not
  alternatives.
- Owner: a node's own `owner`, else the owner of its first parent, recursively. A decision on a node
  is refused to anyone but its owner, if it has one (as today).
- The decide request (`POST /api/p/NAME/decide`, MCP, CLI) is unchanged; `reject` lists alternatives.

## 6. Browser

- The tree from the root: each node under its first parent, with "also under X" chips for the others;
  definitions in their own list under the tree; assumptions marked as trusted.
- The focus pane of a node: its parents (with each parent's split status), the node, its parts.
- The decision pane of a node with parts: a table of its parts (id, statement, needed, status) and
  the `complete` and `clash` results, decided as one ("these parts make it").
- The inbox: ready nodes (all parents decided) first, by depth; a node shared by more parents first
  within a depth; mechanical batch as today.

## 7. Agents

`context(node)`: its idea section, the vocabulary it uses (terms, meanings, definitions in force), its
ancestors deduplicated by depth with their reasons, for each parent its co-parts, its parts, rejected
alternatives, what moved. The skill tells the agent where a new statement belongs: under the lowest
nodes it helps prove, as a part; never as a restatement.

## 8. Order of work

1. Core (one change): vocabulary and definitions, the node kinds and edges, the Lean obligations and
   composition, `check`, snapshot fields, runtime (`service` binds operations to implementations,
   assumptions checked as `relies` guarantees were), the old API removed; `examples/auth` migrated as
   the first example; core tests rewritten.
2. In parallel, on top of 1: decisions and ledger (§5); browser and tools (§6); Lean library (§3).
3. In parallel, on top of 2: `examples/keycloak`, `examples/crm`, `bench/generate.py` migrated, their
   ledgers decided again through the browser by an agent playing the developer (labelled as such).
4. Docs (README, SKILL), measurements, and a review.

## 9. As built in phase 1 (core): departures and precisions

Minimal departures from the above, each kept to what the code needed; none from §0.

- **Defined terms in Lean.** The vocabulary module (`FrFlowGen/<KB>/Domain.lean`) holds the domain
  types, the `define`s, and each definition in force: a type as an `abbrev`, a term as a `def` over the
  terms its definition mentions. A node's own declarations (`claim`, `post`, `rule`) take every term
  they mention as a binder, defined or not; every statement (`complete`, `holds`, the tries, `impl`,
  `root_impl`) applies them to the definitions in force, so it is over the open terms only. A node's
  Lean thus does not change when a term it uses gets a definition; only its statements do.
- **Typing.** A `Param` of an opaque type (`good: Item.T => Boolean`) cannot be applied, in Scala, to
  the concrete type a definition fixes (`Book`): parts below a type's definition are written in
  concrete terms (or in terms of concrete type, defined as in `examples/auth`).
- **Operations.** A term is an operation when some contract or assumption is about it (`op`). The
  root's `idle` replaces the operations its statement mentions (through the definitions) by doing
  nothing; a root that mentions no operation yet has no `idle`.
- **Alternative definitions.** With two definitions of one term and neither chosen, the nodes that use
  the term are not checked (status `waiting`); examples and `service` use the first listed until then.
  The choice is read from the ledger (an accepted definition is in force).
- **Obligations.** `nontrivial` is gone (the root's `idle` says the root says something); `feasible`
  stays as specified. `needed_i` with one part is named `vacuous`. Lean modules per node: `Spec`
  (claim and statements), `Auto` (`complete`), `Theorems` (`holds`), `Impl` (`impl`, a module so that
  `RootImpl.lean` can import it), `Checks` (tries with a small heartbeat budget, and `check`, `cover_X`,
  `expect_i`, `feasible`), `Eval`; and `FrFlowGen/<KB>/RootImpl.lean`, elaborated with the root's check.
  `holds` binds every open term of the nodes it goes through. A contract keeping an invariant no longer
  has `inv_X`: the invariant's `complete` (with the keeper needed) is that proof; `cover_X` stays on the
  contract. `idle` applies to the root only (the contract-level `idle` is gone, as specified).
- **Expectations** are `node.expects(statement)(formula: => Boolean)`, a formula over the vocabulary
  (an operation is mentioned by its `Param`), proven from the node's claim.
- **Imports.** `kb.uses(other, dir)(contracts*)` brings each contract as a leaf: the node object is the
  other knowledge base's (its `content`, parents included, is the same as there, so its decisions there
  hold), but here it has no parents and no kept invariants; the definitions its statement uses come
  with it. Its `parentChain` here is the one its decision there recorded.
- **Snapshot.** Besides §4: per node `status` (the check of its statement: `proven`, `open`, `failed`,
  `waiting`, `unchecked`, `timeout`, `informal`; null for definitions and design nodes), `leaf` (a claim
  no part proves), `rootImpl` (on the root), `obligations` (each with its statement), `holds` (its
  statement), `relies` (the contracts its code calls). Gone: `parent`, `link`, `obligation`,
  `rootTheorem`, `reliances`, `reliedOnBy`, `roots`. The content of a node carries `kind`, `parents`,
  `op`, `replaces`; `vocabulary` lists every term it mentions (not only those first used on its path).
  `ContentFormat` and `CheckerVersion` are 4.
- **Decisions (phase 1 only).** `waitsFor` is the first parent not accepted, else the first definition
  used or contract called not accepted; alternatives are `replaces` and two definitions of one term;
  the owner is a node's own, else its first parent's. Everything else of §5 is phase 2.
