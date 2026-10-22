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
  `ContentFormat` and `CheckerVersion` are 4 (phase 2a adds `parts` to the content without changing
  `ContentFormat`: a snapshot without it decides as before, and decisions without it are not reviewed for it).

### As built in phase 2a (decisions)

- **Content.** A statement's content (claim, contract, assumption, invariant) carries `parts`: the ids
  of its statement parts, in the model's order (a design node under it is not a part of what it
  says: it governs code). Definitions and design nodes have no `parts` in their content. An imported
  node carries the parts its decision there recorded. In the annotated snapshot, `content.parts` is the
  parts now, and the content each decision bound is in `history` (entries with `binds: true`; the last
  is what the node is bound to, `decision` being the choice): their `parts` against `content.parts` are
  the parts added and removed under the cause `parts`. A decision recorded before (no `parts` in its
  content) is not reviewed for its parts, as for any field a later format added: old ledgers load as
  they are, and a decided node no longer in the model is listed under `gone`, as before.
- **Causes.** `self`: what the node says itself changed, that is its content without `parts` and
  `parents`, and with the calls that place it (`.under(...)`) taken out of its `definition` source; a
  design node rests on its parents' place, so for it `parents` stays part of what it says. `parts`: the
  set of its parts changed (order aside; a part renamed is the same part). `above`: the node's
  `parentChain` changed. `parentChain` is unchanged from phase 1: the sorted chains of its parents, of the
  definitions in force it uses and of the contracts its code calls, each chain hashing the meaning of
  that node with its own `parentChain`; a node's meaning has no `parts` or `parents`, so a sibling added
  reviews the parent only, and a change above a diamond moves the shared node's `parentChain` once: one
  cause, whatever the number of paths. A node placed under another parent is reviewed for `above` (it
  rests on more), and that parent for `parts`; it does not say anything else (`self` is not set).
- **Accepting.** Accepting a node under review whose own content did not change (only `above`, `parts`,
  what follows from elsewhere) is recorded as a `confirm`: the reason it was chosen stays, and the new
  parts are bound with it. A node named to `confirm` is confirmed only once all it rests on (its
  parents, the definitions it uses, the contracts its code calls) is accepted, parents first.
- **Mechanical.** Any node under review but a definition or a design node (the root included) whose
  causes are among `self`, `above` and `parts`, whose own content (as for `self`, without what follows
  from elsewhere: the types it uses, how its examples print, a proven implementation) did not change,
  that `unproven` says nothing of (a leaf claim aside), whose examples pass, and, under `parts`, whose
  `split` has `complete` proven, every part `needed` and `clash` not `clash` (see "Fixes after the migrations").
- **Below.** `below` (what accepting a change can act on) follows everything that rests on the node,
  however far down: its parts, the nodes using a definition, the callers of a contract, the keepers of an
  invariant, and what rests on those, through the decisions listed only; each once, sorted parents first
  (the snapshot's `order`). The root's change also lists the decisions outside it, as before.
- **Alternatives.** `Decisions.alternatives(a, b)` (one replaces the other, or both define one term) is
  the one rule: `decide` refuses anything else in `reject`, and the annotated snapshot gives each node
  `rivals` (new): the ids of the nodes of the model that are its alternatives (in `order`). The field
  `alternatives` is unchanged: the alternatives the ledger says were rejected for it, as objects
  `{id, content}`. No other annotated field was renamed or removed.
- **Unchanged.** `waitsFor` (a proposal, or a node whose `above` moved, waits for the first of its
  parents, then of the definitions it uses and the contracts its code calls, that is not accepted; any
  node waits for a parent proposed or rejected), `conditionsAbove` (all ancestors, each once), the owner
  (its own, else its first parent's, recursively; others are refused), signing, the ledger format and its
  merge driver. `unproven` keeps "nothing below proves it" on a leaf claim: a claim is proven by parts
  or trusted as an assumption, so the CI gate (`complete`) fails on it; `status` lists it as trusted.
  `ContentFormat` and `CheckerVersion` are 4.
- **Decisions (phase 1 only).** `waitsFor` is the first parent not accepted, else the first definition
  used or contract called not accepted; alternatives are `replaces` and two definitions of one term;
  the owner is a node's own, else its first parent's. Everything else of §5 is phase 2.
- **Browser (phase 2).** As §6, with these choices. The tree is drawn from the root, each node under its
  first parent (its card says "also under" the others; selecting a node also draws its other parent edges,
  dashed); nodes under no parent besides the root are drawn beside it; definitions in a row under the
  tree, each card saying what it defines and which nodes use it. Kind badges: root, claim, invariant (a
  claim with `rule`), contract, assumption, definition, design; a "trusted" chip on assumptions and on the
  ids in top-level `trusted`. An edge is coloured by its parent's split (red when Lean shows that part is
  not needed); one label per parent says how its parts make it. A node's pane shows its parents (each with
  its split, whether this node is needed there, and its co-parts), the node by kind (formula/post/rule, the
  vocabulary it mentions with meanings and the definition fixing each, the definitions in force it uses),
  then its parts. The parts table (id, statement, needed, status, then `complete` and `clash`; on the root
  also `idle`, `root_impl` and the trusted list) is in the decision while the node waits for the
  developer, so a node with parts is accepted with them ("these parts make it"). Alternatives are computed
  as core's `Decisions.alternatives` (plus any ids core lists in `alternatives`); accepting a node sends
  every live alternative in `reject` (asked to confirm when one was decided before). Inbox: "ready" means
  every parent and every definition used is accepted (and core's `waitsFor` is empty), ordered by depth
  (the longest way from a node with no parents), then by number of parents (more first); the mechanical
  batch next; the rest under "After the decisions above them", each with what it waits on. Header:
  splits proven (of the formal splits), `root_impl`, the size of the trusted list. Cause `parts` shows the
  parts added and removed when the decided content records `parts`.

### Fixes after the migrations

What the migrations of `examples/keycloak` and `examples/crm` found in the core, fixed:

- **Equations of a `match`, made where it is declared.** Lean 4.35 makes the equations of a `match` (and,
  for one with overlapping patterns, an auxiliary `_sparseCasesOn` named after them) in the first module
  that uses them (`grind`, `simp`); two modules that both did failed in a third importing them
  ("environment already contains `f.match_1.congr_eq_1._sparseCasesOn_2`"). The kernel's command
  `frflow_match_eqns` (`lean/FrFlow/MatchEqns.lean`) makes them in the module that declares the `match`,
  and the vocabulary module and every `Spec` end with it: the modules that use them import them. The
  translation is unchanged: expanding a wildcard into the remaining constructors would cover an enum only,
  not `Option`, `List`, a literal or a nested pattern, which clash the same way.
- **A defined term is evaluated where it is used.** `param := expr` keeps its Scala value as a thunk
  (`Lifted.value` evaluates it on each use, under the bindings in force), so a term defined by an
  expression over parameters (`sessions := stateAfter(history.value).sessions`) no longer reads them when
  the model loads.
- **A bypass is a call on the adapter.** `bypasses` (a governed file calling an adapter's method past
  `service`) flags a call only on the adapter: on a name the file declares of one of the adapter file's
  classes (`db: Db`) or binds to one (`val db = Db.open(...)`, `new Db(...)`), on such a class, or on the
  value of a model parameter of that type (`database.value`). A list's `find` or a response's `write` is no
  longer taken for the adapter's method of that name.
- **Tries in plain words.** A try's result (in `checks.json`, the snapshot's `split`, `check`'s output and
  the browser) says what Lean showed, no longer read backwards: each part `needed` or `not-needed` (with
  one part, `vacuous` gives the same two), `clash` or `no-clash`, `unsat` or `not-unsat`, the root's `idle`
  or `not-idle`, an expectation's `vacuous_expect_i` `vacuous` or `not-vacuous`; `unchecked`, `timeout`
  and `informal` as before when there is no result. `complete` and the obligations stay `proven`, `open`,
  `failed`. `Result.fine` (nothing to do) is `proven` or a try showing nothing wrong. The snapshot's
  `idle` on the root is unchanged (what doing nothing is, when Lean shows it meets the root; else null),
  and a kept invariant's status stays in its own words (`proven` when the contract is needed, `open` when
  not). `CheckerVersion` is 5: results recorded before are checked again.
- **Small API gaps.** `Node.assumption` takes `idea` and `owner`, on a fact and on an operation (the latter
  through `AssumptionOn`, so both overloads may have defaults: `Node.assumption(op)(id, statement, why,
  idea = "...")(post)` reads as before). `Def` and `Param` apply to four and five arguments. `impl` is proven
  from the promises of the operations the code calls (itself, or through the `define`s it calls:
  `Generate.calls`), not of those a term it reads is defined with; `callees` (that too) still orders the
  composition of `root_impl`, and is what a node's code rests on (`relies`, `parentChain`), so no decision
  moves. Keycloak's authored `impl` of Introspect no longer introduces HandleRequest's promise.
- **End-to-end tests reuse what is current.** The CRM's and Auth's "proven" tests check the example's own
  workspace (`examples/<x>`, kernel `../../../lean`), as `run check` does: its Lean build and recorded
  results are reused while current, so after a check they take seconds. `LeanSuite` still checks small
  knowledge bases from scratch. Automation is not tried on an obligation the proof file proves (the
  `Auto` module is then empty); when it is tried and fails, `complete`'s detail starts with "automation
  gave up: write theorem complete : Obl.complete in lean/Proofs/<KB>/<N>.lean (run `scaffold <N>`)". Its
  budget stays Lean's default (200000 heartbeats): measured, a `complete` automation proves takes up to
  72000 (Keycloak's root; the CRM's 69000), and one it cannot prove gives up after 8000 to 200000 (the
  CRM's WritesTakeEffect and WritesInCompany use all of it, about 20 s each); a smaller budget would save
  seconds and could lose proofs a model needs.
- **A list's elements as a set.** `xs.toSet` translates to the list's membership (`fun y => y ∈ xs`, the
  shape of a `Set` in Lean), so code can build a hash set once and test membership in constant time
  (`val there = shelf.toSet; picked.filter(b => there.contains(b))`), proven like `xs.contains`.
