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
| claim | `Node.claim(id, statement, why, idea = "")(formula)` | a proposition over the vocabulary (`formula: => Boolean`, lifted) | `def claim : Prop` over its open terms |
| root | a claim with no parents | the purpose | as a claim, plus `idle` |
| contract | `Node.contract(op)(id, statement, why)(post)` with `op: Param[(A, B) => R]` | every call of `op` meets `post`; the claim is `∀ a b, post(a, b, op(a, b))` | as a claim; `impl` when code is attached |
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
`formal = false`, `Opaque`, `Param`, `define`, `forall`/`exists`.

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
| `restates` (n = 1) | tried: `∀ U, N → C1` | as above | if proven (with `complete`), N says what its part says: a warning |
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
  removing a part puts the parent up for review (cause `parts`).
- Causes (`causes`): `self` (its content changed), `above` (a parent's or a definition's decided
  content changed: any of them), `parts` (its list of parts changed), `code`, `revisit`, `merged`.
- Mechanical (one batch, as today): a node under review whose own meaning did not change and whose
  obligations Lean proves again; for `parts`, when `complete` is proven and every part is needed.
- A proposal waits until all its parents and the definitions it uses are accepted (`waitsFor`: the
  first that is not).
- Alternatives: `replaces`, and two definitions of one term. Siblings under one parent are parts, not
  alternatives.
- The decide request (`POST /api/p/NAME/decide`, MCP, CLI) is unchanged; `reject` lists alternatives.

## 6. Browser

The browser moved to the `web-view` branch (r17); the developer's flow comes to the CLI.

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
- **Snapshot.** Besides §4: per node `status` (the check of its statement: `proven`, `open`, `failed`,
  `waiting`, `unchecked`, `timeout`, `informal`; null for definitions and design nodes), `leaf` (a claim
  no part proves), `rootImpl` (on the root), `obligations` (each with its statement), `holds` (its
  statement), `relies` (the contracts its code calls). Gone: `parent`, `link`, `obligation`,
  `rootTheorem`, `reliances`, `reliedOnBy`, `roots`. The content of a node carries `kind`, `parents`,
  `op`, `replaces`; `vocabulary` lists every term it mentions (not only those first used on its path).
  `CheckerVersion` versions how checks are run.

### As built in phase 2a (decisions)

- **Content.** A statement's content (claim, contract, assumption, invariant) carries `parts`: the ids
  of its statement parts, in the model's order (a design node under it is not a part of what it
  says: it governs code). Definitions and design nodes have no `parts` in their content. In the annotated snapshot, `content.parts` is the
  parts now, and the content each decision bound is in `history` (entries with `binds: true`; the last
  is what the node is bound to, `decision` being the choice): their `parts` against `content.parts` are
  the parts added and removed under the cause `parts`. A decided node no longer in the model is listed
  under `gone`.
- **Causes.** `self`: what the node says itself changed, that is its content without `parts` and
  `parents`, and with the calls that place it (`.under(...)`) taken out of its `definition` source; a
  design node rests on its parents' place, so for it `parents` stays part of what it says. `parts`: the
  set of its parts changed (order aside). `above`: the node's
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
  node waits for a parent proposed or rejected), signing, the ledger format. `unproven` keeps "nothing below proves it" on a leaf claim: a claim is proven by parts
  or trusted as an assumption, so the CI gate (`complete`) fails on it; `status` lists it as trusted.
- **Decisions (phase 1 only).** `waitsFor` is the first parent not accepted, else the first definition
  used or contract called not accepted; alternatives are `replaces` and two definitions of one term.
  Everything else of §5 is phase 2.
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
- **Tries in plain words.** A try's result (in `checks.json`, the snapshot's `split`, `check`'s output and
  the browser) says what Lean showed, no longer read backwards: each part `needed` or `not-needed` (with
  one part, `vacuous` gives the same two), `clash` or `no-clash`, `unsat` or `not-unsat`, the root's `idle`
  or `not-idle`, an expectation's `vacuous_expect_i` `vacuous` or `not-vacuous`; `unchecked`, `timeout`
  and `informal` as before when there is no result. `complete` and the obligations stay `proven`, `open`,
  `failed`. `Result.fine` (nothing to do) is `proven` or a try showing nothing wrong. The snapshot's
  `idle` on the root is unchanged (what doing nothing is, when Lean shows it meets the root; else null),
  and a kept invariant's status stays in its own words (`proven` when the contract is needed, `open` when
  not). `CheckerVersion` is 5: results recorded before are checked again.
- **Small API gaps.** `Node.assumption` takes `idea`, on a fact and on an operation (the latter
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

### Witnesses (after the documentation review)

`feasible` is asked of an authored `complete` unless the node is witnessed: it has proven code, it is
an assumption, or all its parts are witnessed. (Before: any proven code below the node waived it, so a
split with a part nothing proves could rest on a contradiction.) Assumptions count as witnessed: their
joint consistency is trusted, and a check of it over the whole DAG (`∃` open terms meeting every
assumption, the reference defines as witnesses of the ports) is future work.

### Speed (after the benchmark on the DAG)

Measured on `bench/generate.py`, four cores. A cold check went from 121 s to 51 s at 54 nodes, and is
now linear (about 0.85 s a node). The causes, and what changed:

- **Every generated module loaded the whole of Lean.** `FrFlow.Attr` and `FrFlow.MatchEqns` imported
  `Lean` (for `register_simp_attr` and the match equations): 1.35 s to start each module, against
  0.6 s for one importing nothing, three to five modules a node. They import the two modules they use.
- **A try that fails runs to its budget.** In a sound DAG nearly every try fails (no part is
  redundant, nothing clashes), and each ran `frflow_auto` to 40000 heartbeats, longer the bigger the
  statement (Group0's seven tries: 6 s). The budget is 4000: the tries the tests expect to succeed
  still do (a redundant part, a clash, an idle root), and a failed one costs a tenth.
- **A change below re-checked every ancestor.** A node's check hash read its parts' full hashes (their
  proofs and code); it reads their statements, and the root reads everything (`root_impl`). A code
  change re-checks its contract and the root (20 s at 305 nodes, 70 s before at 95).
- **A group's statement restated every service.** The benchmark's root, `Served` and the groups said
  every service's promise in one conjunction, and one invariant had every contract as a part: those
  statements, and their proofs and tries, grew with the project. Each group and area now has a word
  of the vocabulary (`group0Ok`, a definition over its five services), the root says `catalogOk`, and
  each group keeps its own floor (an invariant with five keepers). Matching (the `complete` tried
  first) unfolds the defined terms a node mentions and none of its parts does, so a group, an area and
  the root are proven by matching, not by `frflow_auto`.
- **`KnowledgeBase.children` scanned every node** for each call (`parts`, everywhere): indexed once.
- **A vocabulary module's file name is plain.** A term Lean reads as a keyword is escaped in Lean
  (`«matches»`), but its module (`Domain/Def_matches.lean`) is not: the escape is not a file name every
  file system or JVM encoding takes (the CRM's check failed on it).
- **A cached node is kept only while its parts are proven.** Since a part's code no longer changes its
  parents' hash, a parent whose part has stopped being proven is checked again (it waits for it), and
  its hash reads its parts' `holds` statements, which name the leaves below them.

### Honest tries, review by meaning (after the r16 review)

- **A try says what Lean did.** A try that fails shows nothing: Lean found no proof within its budget.
  The status keys are unchanged (the browser reads them), and the details say so: a part `needed` reads
  "Lean found no proof that N holds without it (a try)", the root `not-idle` "Lean found no proof that
  doing nothing (…) meets it (a try)", and so for `no-clash`, `not-unsat`, `not-vacuous`. A proven try
  (`not-needed`, `clash`, `unsat`, `idle`, `restates`) is a proof, and says what it shows.
- **`idle` at Lean's default budget.** It is one try per knowledge base, and at 4000 heartbeats it gave
  up on a CRM-sized root that only prohibits (proven idle in under a second at the default). The other
  tries keep 4000.
- **A kept invariant's status** comes from what is proven: the coverage of its view and the
  invariant's `complete` (the contract among its parts), and `open` when Lean proves the invariant
  holds without the contract (`not-needed`). A failed `needed` try no longer makes it `proven`; the
  detail says "needed: not shown otherwise" apart.
- **Mechanical acceptance of a change of parts** still asks that `complete` is proven and that the tries
  ran and show nothing wrong (no part `not-needed`, no `clash`). Read honestly, this is not "each part
  is needed" but "Lean proves the parts make it, and finds nothing redundant or contradictory": the rule's
  intent, since the parts added are decided on their own; it stands.
- **`restates`.** A node with one part C is tried for `N → C` (4000 heartbeats). With `complete`, N and C
  are then equivalent: `status` warns "N says what C says: merge them, or say what N adds"
  (`Result.isLimit`, like `idle`: not an obligation).
- **Review follows meaning.** Rewording a formal node (its statement; its `why` already did not
  cascade), with what Lean reads unchanged (sources, substitutions, vocabulary, uses), reviews that node
  (`self`) and not what rests on it: a node's `above` is not set when its recorded chain is met again
  with every such reworded node above it taken as it was decided then (`Decisions.View.reworded`). The
  hashes and the ledger are unchanged, so existing decisions read as before. The reworded node's review
  lists the decisions below it (`below`, kind `accepted`): what may be affected, to revisit by name. A
  `formal = false` node is its words: rewording it cascades as before; so does any change of a formula.
- **`unsat` stays.** `feasible` is asked only of an authored `complete` with nothing witnessing the
  parts; a leaf claim or a node proven by automation is never asked it, and a contradictory one makes
  everything above it provable. `unsat` is the one guard there (cheap, and one-sided as the others).
- `CheckerVersion` is 6: results recorded before are checked again.

### Browser (after the r16 developer review)

- **Asking for a change.** One "Ask for a change" box on every node (proposed, under review or
  accepted) replaces "Send back to the agent" and "Ask the agent". A request records the version of the
  node asked about (`seen`); the node is "with the agent" until the agent answers or the node changes:
  it is not under "Waiting for you", the default action skips it, and its pane offers to withdraw the
  request instead of accepting.
- **What waits on the agent is named.** The inbox lists each rejected node still in the model, with
  who rejected it and why, and each node resting on one; a rejected node's pane says it is rejected
  (it said "Accepted").
- **Counts.** "N waiting for you" counts decisions only (nodes waiting for you, and gone nodes), as the
  CLI's inbox does; answers to read, nodes with the agent and decisions to sign are counted apart. The
  browser had added answered requests to the decisions.
- **Layout.** The legend is docked under the graph and folds; the graph fits the pane down to 80%, scrolls
  beyond that, and scrolls to the node selected.
- **Proven code, and authored proofs, in words.** A contract's code reads as the CLI words it: "proven
  down to its code: proven define D; running code R checked against it", or "checked by running". An
  authored `complete` says which parts the proof refers to (by name, outside comments) and whether it
  needed `feasible`; the Lean is folded.

### Agent loop (after the r16 developer review)

- **The agent reads why a node was rejected.** `inbox` lists each rejected node with who rejected it
  and their reason, and `context` prints the rejection: a reason that asks for something is answered
  by a node in its place, not only by removing the rejected one.
- **Authored proofs introduce binders by name.** `scaffold` starts each stub with `unfold Obl.X`,
  `frflow_intro` (FrFlow's tactic: every binder by its generated name, the open terms and `h_<Part>`)
  and `simp only [frflow_defs] at *`, then the goal they leave as a comment; `check` prints that same
  goal when automation gives up (before, `frflow_auto`'s normal form, which the recipe does not reach).
  A proof using the names survives a part or a term added.
- **Code diffs use an index of their own.** `Git.diff` compares the decision's tree with the files as
  they are through a temporary index, so a file git does not track (a new project before its first
  commit) is diffed as it is, not shown as deleted.
- **One wording for code**: a contract is "proven down to its code" when its implementation is a
  proven `define`, with any running code beside it named as "checked against it"; a plain
  implementation is "checked by running"; code only design nodes govern is "reviewed only" (`status`,
  the tree). Invariants show as `invariant` in the tree and `context`.
- **`answer` in the CLI** (`<kb>/run answer REQUEST|NODE TEXT`), as MCP's, for agents without MCP.

### The CRM's one store (after the r16 review)

- **The CRM's root says what its sentence says.** Reads and writes share one store: `store`, `shares`
  and `expiries` are defined from `runOf(history)` (CrmRun, as keycloak's ServerRun; before, they were
  open terms apart from the writes' stores), so the root proves that a record a user adds is then found
  by their searches (AddedAreFound: `FrFlow.always` over the events after the add, with RecordsKept). A
  share ends at its time whether or not the job ran: a search compares its expiry with the clock
  (LiveShares; ShareRows, which would trust the job's schedule, is rejected in the ledger). Two root
  expectations check the sentence on a concrete store and history. Gone: the one-part chains
  FindRecords and SalesScreen (now SearchesMatch, over both screens) and the seven root terms a
  definition fixed one-to-one (ten definitions became five). The running read side binds the tables
  directly and the new event log as `history`; a test replays the log against the tables.
