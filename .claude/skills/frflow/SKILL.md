---
name: frflow
description: >-
  Develop a system with FrFlow: one root (the idea's purpose) refined by a DAG
  of small statements in the domain's words, each proven in Lean from its
  parts and decided by the developer. Use when turning an idea
  into a root, proposing or changing nodes, introducing domain terms, adding
  examples, answering the developer's requests, proving a split, or attaching
  an implementation; or when the work touches IDEA.md, `Node.claim`,
  `Node.contract`, `Node.assumption`, `Node.definition`, `Node.design`,
  `Node.invariant`, `.under`, `.replaces`, `implementProven` or `service`.
---

# Developing with FrFlow

The developer writes the idea in `IDEA.md`. You write Scala nodes: one root,
and below it parts that together prove it, down to contracts on the code. Lean
proves each split; the developer decides every node, and
whatever moves under a decision puts the node back up for review. The README
explains the method and `docs/DAG.md` the design; this file holds your rules.
To start a project, follow the README's "New project".

## Rules

1. **You propose; the developer decides.** Never edit `.frflow/ledger.json`,
   decide for the developer, create a signing key, or add files to
   `.frflow/keys/`. If `status` says decisions are not signed, tell the
   developer: each decision they take through the CLI is signed with their key,
   and its public half goes in `.frflow/keys/`, committed.
2. **One statement per node**, one sentence in the developer's domain words,
   and the formula says exactly that sentence. A formula that packs several
   independent properties is split into parts.
3. **A part is never a restatement.** A node that only says its parent again,
   in more detail, is not a node: say what the domain adds (a concept, a
   mechanism, a rule), or attach the contract to the parent directly.
4. **2 to 5 parts per parent.** More asks for an intermediate concept, a node
   between them.
5. **The root is stated as exactly**: what users can do and what must never
   happen, together, so a system doing nothing does not meet it.
6. **Introduce the domain by definitions.** Leave a concept open (`Opaque`,
   `Param`) where the idea is general; fix it with a `Node.definition` where
   the domain says what it is. Each term has one meaning (`means`) and at most
   one definition.
7. **`why` carries the theory**: why this step, and what it assumes about the
   world. Every `Opaque` and `Param` says what it means and where its value
   comes from.
8. **Offer real alternatives** where a step has more than one reasonable
   design: the second `.replaces` the first, its `why` covering the trade-off.
9. **Never weaken a node to make a proof go through.** A false split means a
   part is wrong or missing. If the idea or a decided node is wrong, say so and
   propose a change.
10. **Never edit generated Lean** (`lean/FrFlowGen/`, `lean/FrFlowAudit/`).
    Lean you write goes only in `lean/Proofs/<KB>/`.
11. **Every source file is governed by one node**: a contract's or assumption's
    implementation, or a design node. Keep production wiring (the call to
    `service`) in a design node's file.
12. **Say what is not modelled**: propose it for `## Not modelled` in
    `IDEA.md`.
13. **Say what waits.** In your `answer`, name the waiting nodes that are
    mechanical.

## The loop

1. `inbox`: requests, rejected nodes (each with who rejected it and why),
   waiting decisions, the summary (`tree` draws the DAG).
2. For each request, read `IDEA.md` and `context NODE`, and `find` where the
   change belongs. Place a new statement **under the lowest nodes it helps
   prove, as a part** (several parents if it serves several). Extend what
   exists; do not add a near-duplicate.
3. Write the proposal with `why` and examples, add it (and any definition) to
   `KnowledgeBase(...)`, then `render` and `check`. Fix failing examples first
   (the code or the contract is wrong, not the proof), then the splits.
   Proposals should reach the developer proven, with passing examples.
4. `answer REQUEST TEXT`: name the proposals, the trade-off, what is left
   open.
5. After the developer decides, read each rejected node's reason (in `inbox`,
   and with the decision in `context`). If it asks for something, propose a
   node in its place that does it, under the same parents, its `why` saying
   what the reason asked; then (or if it asks for nothing) remove the rejected
   node, move what was under it under the node chosen, and drop its name from
   other statements.
6. When the inbox says the developer asks to revisit a node, propose a change,
   or `answer NODE TEXT` why it still holds.

## Tools

The knowledge base's CLI: `bin/frflow <kb> COMMAND` from the repository root
(it compiles with sbt on first use and after a change; `sbt "<kb>/run COMMAND"`
works too, slower, with sbt's `[info]` before each line). Piped, the output is
plain ASCII and not cut to a width; `--json` on `tree`, `show`, `inbox`,
`status` and `check` prints the typed value, each node in brief.

| command | use |
|---|---|
| `inbox` | Start here: requests, clean-up, waiting decisions, then the summary. |
| `context NODE` | Everything on a node (`show NODE --full`): what changed, its decision, the idea it is decided against, its formal statement, where it sits (parents, co-parts under each, parts, design nodes, the contracts its code calls with their promises), what it rests on with every reason, the vocabulary and the functions it names, its proofs and obligations in Lean, all its examples and code, its decisions, rejected alternatives and requests. |
| `tree [NODE]`, `show NODE`, `diff NODE` | The DAG (or what is below NODE); a node in about a screen; what changed since it was decided. |
| `find WORDS\|PATH` | Which nodes govern a file (a path from the project or from the repository root), or what mentions some words: nodes, reasons, rejected options, gone nodes, the idea, Not modelled. |
| `render` | Rebuild from the Scala; compile errors and structural problems come back here. |
| `check [NODE]` | Prove what changed and evaluate the examples in Lean. Slow. A `timeout` is not a failure: run it again. |
| `status` | The tree and the summary (decisions, proofs, examples in Lean, what is trusted), then the warnings; exits 1 unless the knowledge base is complete. |
| `scaffold NODE` | Stubs in the node's proof file for what the last check left open; nothing when it left nothing open. |
| `answer REQUEST TEXT` | Reply to a request; `answer NODE TEXT` tells the developer about work they did not ask for. |

`ci` is for CI: `check`, then `status`. Exit codes: 0 fine; 1 not complete, or
refused; 2 a usage error (an unknown node too).

## Writing nodes

From `examples/auth`:

```scala
val User     = Opaque("User", "a person who uses the system")
val access   = Param[(User.T, Resource.T) => Boolean]("access", "whether the system lets the user access the resource")
val admit    = Param[(String, Path) => Option[UserId]]("admit", "the system's decision on a request (a token and a path): the user it is admitted on behalf of, if any")

val accessExactly = Node.claim("AccessExactly",
  "A user gets access to a resource exactly when they are signed in and authorized for it.", why = "...")(
  forall((u: User.T, r: Resource.T) => access(u, r) == (signedIn(u) && authorized(u, r))))

val identities = Node.definition("Identities", "Users are named by ids, and resources are paths.", why = "...")(
  User := of[UserId], Resource := of[Path])
val requests = Node.definition("Requests", "A user has access to a path when some request for it is admitted on their behalf.", why = "...")(
  access := ((u: UserId, p: Path) => exists((t: String) => admit(t, p) == Some(u))))

val grantLetsIn = Node.claim("GrantLetsIn",
  "A request whose token was issued to a user with a grant for the path is admitted on their behalf.", why = "...")(
  forall((t: String, p: Path) => sessions(t).forall(u => grants.value.contains(Grant(u, p)) ==> (admit(t, p) == Some(u)))))
  .under(accessExactly)
```

**Vocabulary.** `Opaque("Name", means)` is a domain type (`Name.T`);
`Param[T]("name", means)` a term: a fact of the world (`grants`, `enabled`) or
an operation of the system (`admit`), a function some contract or assumption is
about and some code implements. The val's name and the name given must be the
same. A `define { ... }` is a named function in the Scala Lean translates, run
as Scala and proven in Lean. An open term is universally quantified: what is
proven holds for every value of it.

| Constructor | What it is |
|---|---|
| `Node.claim(id, statement, why, idea = "", formal = true)(formula)` | a proposition (`=> Boolean`). The one claim with no parents is the root. |
| `Node.contract(op)(id, statement, why, idea, formal)((a, b, r) => post)` | every call of `op: Param[(A, B) => R]` meets `post`; code is attached to `op`. |
| `Node.assumption(op)(id, statement, why, idea)((a, b, r) => post)` | what the outside does on an operation (a database, a store, the clock): trusted, a hypothesis of `root_impl`; its adapter is checked against it. |
| `Node.assumption(id, statement, why, idea)(formula)` | a fact of the world, trusted (tokens are fresh); checked at run time where it can be computed. |
| `Node.definition(id, statement, why)(Opaque := of[T], param := expr, ...)` | fixes terms; decided, not proven; no parents. Two definitions of one term are alternatives. |
| `Node.invariant[A, B](id, statement, why, scope = Nil, idea, formal)(rule)` | a rule over pairs (a reader, a record), stated once; a claim whose parts are the contracts that keep it. |
| `Node.design(id, statement, why, idea)(files*)` | governs code no proof covers (wiring, an HTTP API, a convention); under the nodes it serves. |

Edges and extras (chained on a node):

- `.under(p1, p2, ...)`: a part of each. Declare parents first (a `val` used
  before it is defined is `null`, and `under` refuses it). Contracts and
  assumptions may have no parents only when code calls their operation.
- `.replaces(other)`: an alternative; accepting one rejects the other.
- `.keeps(inv)((a, b, r) => pairs)` on a contract: the pairs a call shows to
  the invariant (`result.map(r => (user, r))`); the pairs are about the one
  input of the rule's first type. Or
  `.exempt(inv, "why it shows none")`, on a contract or a design node in the
  invariant's scope. Declare the invariant before the contracts.
- `.examples(bindings*)(expect(a, b, r, note), reject(a, b, r, note), ...)` on
  a contract or an assumption on an operation (see Examples).
- `.checkedBy((a, b, r) => ...)`: when the post reads all the data, a cheap
  check of the result alone, run by `service` on every call; Lean proves the
  post implies it. An assumption on an operation whose post reads all the
  data needs one.
- `.expects(statement)(formula)` on any node: a consequence the developer
  expects, proven from the node. Propose some for a new node.
- `idea = "Section"`: the `## ` section of `IDEA.md` the node is decided
  against (the root takes the title and lead). A section no node names is a
  warning.
- `KnowledgeBase(name, idea = "IDEA.md")(every node, definitions included)`.

**Where it belongs.** A claim states a property in the domain's terms; a
contract states it for one call of an operation, so each result can be
checked; an assumption states what you cannot prove (a port, a world fact).
When a part needs a concept the vocabulary lacks (a session, a token), add a
definition and write the part in its terms. State machines: a `define` folds
the step over the history, a definition says the domain's terms are what it
reaches, and the step's contract is a leaf (Keycloak's `stateAfter`,
`ServerRun`, `HandleRequest`).

**Examples.** Every contract needs at least one `expect` and one `reject`, and
expects with different results. Bind every parameter the post reads
(`grants.bind(...)`); give a lookup as `param.bindTable(Map(k -> v))` so Lean
can evaluate it. Defined terms and the operations other code implements are
bound for you. Lean evaluates each example whose parameters are values, and
probes near them (`probe_j`). "Lean and Scala disagree" means the translation
is wrong: report it; never change the example or the code to hide it.

**Implementations.** `kb.implementProven(contract)(define {...})`: Lean proves
the define meets the contract (`impl`) and the root holds of it (`root_impl`).
`implementProven(c)(define {...}, (a, b) => fast)`: the fast code runs (an
index, SQL), checked to return what the define does on every combination of
the examples' inputs and on varied data; this is how an assumption's adapter is
attached. `implement(contract)((a, b) => plain Scala)`: not proven, checked on
the examples, every combination of their inputs, and every call. Code calls
another operation through its `Param` (`fetch(user, query)`); Lean proves the
caller from that operation's contract or assumption, never its code, and
`service` binds it to that code. Code never calls its own operation.
Production calls `knowledge.service(contract)(bindings*)`, which checks every
result; facts that decide access come from bound parameters over the system's
data, never from the result.

## What check reports, and what to do

Per node with parts: `complete` (`proven`, `open`, `failed`); each part
`needed` or `not-needed` (one part: `vacuous` gives the same two, and
`restates` or `not-restates`); `clash` or `no-clash`; every claim `unsat` or
`not-unsat`; the root `idle` or `not-idle`, and `root_impl`. `unchecked`,
`timeout` and `informal` when there is no result. `status` lists the trusted
list: the hypotheses of `root_impl`. The tries are one-sided: `not-needed`,
`restates`, `clash`, `unsat` and `idle` are proofs; `needed`, `no-clash`,
`not-unsat` and `not-idle` say only that Lean found no proof within the try's
budget (small; Lean's default for `idle`). Never write in a reason that Lean shows a part needed or the root not
idle.

| Report | Means | Do |
|---|---|---|
| `complete` open: "automation gave up" | the parts may not make it | First ask whether they do: usually a part is missing or too weak. If they do, prove it by hand (below), from the goal it prints. |
| Ci `not-needed` | the node holds without Ci | Ci belongs elsewhere (under the node it does help), or another part says too much, or the node says less than meant. Fix the split. |
| `vacuous` (one part) | the node holds whatever its part says | The node says nothing its part adds (often true of every world): strengthen it, or remove it. |
| `restates` (one part; a warning of `status`) | the node and its one part say the same | Merge them, or say what the node adds. |
| `clash` | the parts contradict each other | Fix the parts; a proof from them would prove anything. |
| `unsat` | no world meets the node | Fix the node. |
| `idle` | doing nothing meets the root | The root says only what must not happen: state what users can do. |
| "nothing below proves it" | a claim with no parts | Add the parts or a contract that make it; a fact of the world is an assumption instead. |
| `waiting` | two definitions of a term not yet chosen, or parts not yet proven | Ask the developer to choose; prove the parts. |
| `impl` open | the define does not provably meet the contract | Fix the code, or prove `theorem impl : Obl.impl` by hand. |
| `feasible` open | an authored `complete` with no proven code below | Prove that some world meets all the parts (give the witness). |
| examples fail | the code or the contract is wrong | Fix them before any proof. |
| `ContractViolation` at run time | a result broke the contract or an invariant, or a value breaks an assumption | Fix the code or the data; never the check. |

## Proving by hand

1. Run `scaffold NODE`: it writes `lean/Proofs/<KB>/<Node>.lean` with a stub
   per open obligation, each stating exactly `Obl.<name>`, starting with
   `unfold Obl.<name>`, `frflow_intro` and `simp only [frflow_defs] at *`,
   then the goal these steps leave (as a comment), then `sorry`. `check`
   prints the same goal when automation gave up.
2. `frflow_intro` introduces the open terms by their names and one hypothesis
   per part, `h_<Part>`: refer to them by name, so the proof survives a part
   or a term added later (an `intro` by position does not). Replace `sorry`;
   iterate with `lake env lean Proofs/<KB>/<Node>.lean` in `lean/`, then run
   `check`.
3. The library: `FrFlow.always` (a property kept by every step holds of every
   run), `FrFlow.simulates` (and `simulates_rel`, `simulates_of_inv`: a step
   mirroring an abstract step), `FrFlow.tracks` and `tracks_eq` (the state
   follows the history), `FrFlow.run_snoc` (the last event of a run); for lists
   `FrFlow.filter_filter_of_imp`, `eq_of_nodup_map`, `nodup_map_filter`,
   `nodup_map_snoc`. Shared lemmas of your own go in
   `lean/Proofs/<KB>/Lemmas.lean` (same rules).
4. A proof file holds only theorems with tactic proofs: no `sorry`, `axiom`,
   attributes or metaprograms. It imports only `FrFlowGen.<KB>.Domain`,
   `FrFlowGen.<KB>.<Node>.Spec`, `FrFlow`, `Std`, `Init` and
   `Proofs.<KB>.Lemmas`.
5. Never prove a split from a contradiction in the parts, and never write a
   proof that does not use them.

## The Scala subset

Unsupported Scala is a compile error, `FrFlow: not supported in a model`,
with the usual rewrite for common cases (`count` as `filter(...).length`,
`sum` with `foldLeft`, an `Option`'s `toList` or `map` as a `match`): rewrite
the expression, or make it a `define { ... }`. Supported: fields, case
class constructors, `copy`, `match` (wildcards included), `if`; `==`, `!=`,
`&&`, `||`, `!`, `==>`; `forall`/`exists` over one or two typed binders; on
`List`: `contains`, `exists`, `forall`, `filter`, `filterNot`, `map`,
`flatMap`, `foldLeft`, `find`, `headOption`, `take`, `drop`, `zip`,
`length`/`size`, `isEmpty`/`nonEmpty`, `::`, `++`, `toSet`; on `Option`:
`forall`, `exists`, `contains`, `isDefined`, `isEmpty`, `getOrElse`; on `Map` (a
function from keys to `Option` values in Lean): `get`, `getOrElse`, `contains`,
`updated`, `removed`, `+`, `-`, `==`, `Map(k -> v)`, `Map.empty`; on `Set` (its
membership): `contains`, `+`, `-`, `++`, `intersect`, `subsetOf`, `Set(...)`.
Not `m(k)` (it throws), nor iterating a map or a set. Params (applied or
`.value`), `define`d functions of up to five arguments.

Use `BigInt`: on it `+`, `-`, `*`, unary `-`, `max`, `min`, `<`, `<=`, `>`,
`>=`, and `/`, `%` by a literal; `BigInt(xs.length)` to compare a length with
one. `Int`/`Long` arithmetic is refused (comparisons are not), as is `exists`
over a type holding one. No function-typed fields, no types that
redefine `equals`, no two `define`s with one name.

## Pitfalls

- **Concrete types below a type's definition.** A `Param` of an opaque type
  (`authorized: (User.T, Resource.T) => Boolean`) cannot be applied in Scala to
  the concrete type a definition fixes (`UserId`). Parts below the definition
  are written in concrete terms (`grants.value.contains(Grant(u, p))`), with
  concrete `Param`s and `define`s, and definitions relate the general terms to
  them (as in `examples/auth`).
- **Reserved names.** A `Param` or `Opaque` named `decide`, `max`, `min`, `id`,
  `claim`, `post`, `rule`, `holds`, `complete`, `impl`, `m`, `f`, `h`, `p` or
  `x0`–`x9` (among others) is refused: rename it (Auth's decision is `admit`).
  Other names Lean uses are renamed in the generated Lean (`decide_`, `«end»`):
  use those names in authored proofs.
- **Don't name a val `keeps`** (or after another FrFlow function a model
  calls: `examples`, `checkedBy`, `expect`, `reject`, `define`): it hides
  FrFlow's in that file.
- **Node ids** are identifiers, unique, and differ from every type, function
  and term name; `Lemmas` and `RootImpl` are reserved.
- **To rename a node**, change only its id and its val's name, and move its
  proof file (with its `namespace`); the developer accepts the old one as gone
  and the new one, with "renamed from X" in the reason.
- **Lean 4.35 deprecates `if_pos`/`if_neg` (and `dif_pos`/`dif_neg`)**: in
  authored proofs use `ite_eq_left`/`ite_eq_right` (`dite_eq_left`/
  `dite_eq_right`), or `split` and `simp [h]`.
- **Changing an accepted node** anywhere in its `val` puts it back to review
  (`self`); a change of its formula also reviews what rests on it (`above`),
  and adding or removing a part reviews the parent (`parts`). Rewording a
  statement whose formula is unchanged, a `why`, or adding an example does not
  cascade (the node's review lists what rests on it, to revisit by name). A change to an
  implementation or a governed file reviews the node (`code`): no proof covers
  plain code, so say in your answer what changed and why the invariants it
  touches still hold.
