---
name: frflow
description: >-
  Develop a system with FrFlow: the developer decides, in a browser, a tree of
  Scala nodes, each proven in Lean to refine its parent. Use when turning an
  idea into a root, proposing or changing nodes, adding examples, answering
  the developer's requests, proving a link, or attaching an implementation;
  or when the work touches IDEA.md, `Node.root`, `.refine`, `.instantiate`,
  `.contract`, `.design`, `Node.invariant`, `.relies` or `service`.
---

# Developing with FrFlow

The developer writes the idea in `IDEA.md`. You write Scala nodes: a tree
under each root (one concern of the idea), and invariants across the trees.
Lean proves each link; the developer decides every node in the browser, and
whatever moves under a decision puts the node back up for review. The README
explains the method; this file holds your rules.

## Rules

1. **You propose; the developer decides.** Never edit `.frflow/ledger.json`,
   post to the browser's server, run `frflow serve`, create a signing key, or
   add files to `.frflow/keys/`. If `status` warns of no developer key, tell
   the developer to start the browser and commit `.frflow/keys/`.
2. **Offer real alternatives.** When a step has more than one reasonable
   design, propose each as a sibling node, its `why` covering its trade-off.
   One proposal is fine when the step is obvious.
3. **`why` carries the theory.** Say why this step, and what it assumes about
   the world. For `refine`, why `abs` is faithful; for `instantiate`, why the
   substitutions are the right meanings.
4. **The statement says in plain words what the predicate says.**
5. **Every `Opaque` and `Param` says what it means in the world** and where
   its value comes from: `Param[List[Grant]]("grants", "the grant table as
   stored when the request is decided")`.
6. **Prefer formal nodes.** Use a `design` node only for a decision with no
   formal model (storage, caching, a convention), with the files it governs.
7. **Never weaken a node to make a proof go through.** A false link means the
   child is wrong. If the idea or a decided node is wrong, say so and propose
   a change.
8. **Never edit generated Lean** (`lean/FrFlowGen/`, `lean/FrFlowAudit/`).
   Lean you write goes only in `lean/Proofs/<KB>/`.
9. **Every source file has one owner.** An implementation governs the files
   its expression refers to; other code needs `.governing(paths*)` or a design
   node. Keep production wiring (the call to `service`) in a design node's file.
10. **One model file per concern.** The compiler fails at about 30 nodes in
    one file.
11. **Say what is not modelled**: propose it for `## Not modelled` in
    `IDEA.md` (a `### Section` subsection when it concerns one root).
12. **Say what waits.** In your `answer`, name the waiting nodes that are
    mechanical, and for each decision below a change whose reason says when to
    revisit it, whether that condition may be met.

## The loop

1. `inbox`: requests, rejected nodes to delete, waiting decisions, the tree.
2. For each request, read `context(node)` and `find` where the change belongs.
   Extend the nodes that cover it; do not add a near-duplicate. Write the
   proposals, with `why` and examples, and add them to `KnowledgeBase(...)`.
3. `render`, then `check`. Fix failing examples first (the code or contract is
   wrong, not the proof), then links. Proposals should reach the developer
   proven, with passing examples.
4. `answer(request, text)`: name the proposals, the trade-off, and what is
   left open, including what the contract does not promise.
5. After the developer decides, delete the rejected nodes, move what was below
   them under the node chosen, and drop their names from other statements.
6. When the inbox says the developer asks to revisit a node, propose a change,
   or `answer` with `node` why it still holds.

## Changing nodes

- Changing an accepted node, anywhere in its `val` definition, puts it back
  to review (`self`). A change of meaning also reviews the nodes below
  (`above`); rewording a `why` or adding an example does not.
- To replace an accepted node, propose the new one as its sibling.
- **To rename a node,** change only its id and its val's name, and move its
  proof file (`lean/Proofs/<KB>/<Id>.lean`, with its `namespace`). The browser
  then offers "Renamed to X", which keeps its history.
- A change to an implementation or governed file reviews the node (`code`).
  No proof covers plain code: make sure the examples pass, and say in your
  answer what changed and why the invariants it touches still hold.
- When you change the idea or Not modelled, say which decisions rest on it.
- Formalizing several alternatives can be costly: you may describe them in
  your `answer` first, and formalize the one the developer picks.

## Tools

The MCP server `frflow` (see `.mcp.json`); pass `project` when there are several.

| tool | use |
|---|---|
| `inbox` | Start here: requests, clean-up, waiting decisions, the tree. |
| `context(node)` | What bears on the node: its idea section, vocabulary, path from the root with reasons, alternatives and rejections beside it, reliances, invariants, what moved, decisions below, the obligation, the last failures. |
| `find(query)` | Which nodes govern a file, or what mentions some words: nodes, reasons, rejected options, gone nodes, the idea, Not modelled. |
| `render` | Rebuild from the Scala; compile errors come back here. |
| `check(node?)` | Prove what changed and evaluate the examples in Lean. Slow. A `timeout` is not a failure: run it again. |
| `scaffold(node)` | Stubs in the node's proof file for the obligations the last check left open. |
| `answer(request, text)` | Reply to a request. With `node` and no `request`, answers the open request on that node. |

Without MCP: `sbt "<kb>/run render"`, `check [NODE]`, `status`,
`context NODE`, `find WORDS|PATH`, `scaffold NODE`. `ci` is for CI.

## Writing nodes

```scala
val authenticated = noUnauthorizedAccess.refine[(Token.T, Resource.T) => Option[User.T]]("Authenticated",
  "A request is granted on behalf of a user only if its token belongs to that user and the user is authorized.",
  why = "Users identify themselves with tokens they receive at login. abs: a user is allowed a resource when some token of theirs is.")(
  abs  = decide => (u, r) => exists((t: Token.T) => decide(t, r) == Some(u)),
  spec = decide => forall((t: Token.T, r: Resource.T) => decide(t, r).forall(u => holder(t) == Some(u) && authorized(u, r))))
```

- **`Node.root(id, statement, why, idea = "Section")(spec)`**: one concern,
  over generic types. Make every concept the idea does not define open:
  `Opaque` for types, `Param` for relations and values.
- **`refine(id, statement, why)(abs, spec)`**: `spec m → parent.spec (abs m)`.
- **`instantiate(id, statement, why)(T := of[X], p := expr)`**: fixes open
  terms; holds by substitution.
- **`contract(id, statement, why)(post)`** for a model `(A, B) => R`;
  **`contractVia(...)(abs)(post)`** for a signature of its own. Say what a
  call must do, not only what it must not: doing nothing is listed (`idle`).
- **`Node.invariant[A, B](id, statement, why, scope = ...)(rule)`**: a rule for
  several contracts, over pairs. Declare it before the contracts.
  - Each contract in scope keeps it, listing the pairs a call shows:
    `.keeps(inv)((user, query, result) => result.map(r => (user, r)))`.
  - Or says why not: `.exempt(inv, "it returns no records")`. A design node
    in scope says why it is exempt too.
  - When several inputs have the rule's first type, name the reader:
    `.keeps(inv, reader = 1)(...)` (from 0), or `cover_X` fails.
- **`design(id, statement, why)(files*)`**: no formal model; files tracked.
- **`expects(statement)(m => ...)`**: a consequence the developer expects,
  proven from the spec. Propose some for a new node.
- **`.relies(other, why)`**: the node rests on `other` (often another
  concern); a change to its meaning reviews this node.
  **`.relies(other, why, guarantee)(sees)`** also proves `guarantee` of every
  state `other`'s concern reaches (`rely_<Other>`), and checks it at run time
  on what `sees` returns.
- **`val c = contract.caller("c")`**: code that calls another contract calls
  this parameter, not that contract's code. Lean proves the caller assuming
  only the callee's `post` (`h_c` in `impl` and `root_impl`); the caller rests
  on the callee; bind it at run time to the callee's `service`. Build large
  systems this way: each contract proven once, callers from promises.
- **`formal = false`** (on root, refine, instantiate, contract, contractVia)
  takes a node and all below it out of Lean. Use it only when the subset
  cannot say it or the proof costs more than it gives, and say so in `why`.

**Examples.** Every contract needs at least one `expect` and one `reject`, and
expects with different results. Lean evaluates each example whose parameters
are values; give a lookup as `param.bindTable(Map(k -> v))`. "Lean and Scala
disagree" means the translation is wrong: report it; never change the example
to hide it.

```scala
  .examples(grants.bind(List(Grant(alice, Path("/a")))), sessions.bindTable(Map("t1" -> alice)))(
    expect("t1", Path("/a"), Some(alice), "Alice's token and a grant for /a: she gets in"),
    reject("t1", Path("/b"), Some(alice), "access without a grant is never given"))
```

**Implementations.** Prefer `implementProven(contract)(define {...})`: Lean
proves it meets the contract, and the root holds of the code. Otherwise
`implement(contract)(plain Scala)`, checked on the examples and every
combination of their inputs. Production calls
`knowledge.service(contract)(bindings*)`, which checks each result. Facts that
decide access must come from bound parameters over the system's data, never
from the result.

**State.** Model it as a step `(State, Event) => State` under a root that says
an invariant holds initially and every step keeps it; `FrFlow.always` gives it
for every reachable state (see the CRM's writes).

## The Scala subset

Unsupported Scala is a compile error, `FrFlow: not supported in a model`:
rewrite the expression, or make it a `define { ... }`. Supported: fields, case
class constructors, `copy`, `match`, `if`; `==`, `!=`, `&&`, `||`, `!`, `==>`;
`forall`/`exists` over one or two typed binders; on `List`: `contains`,
`exists`, `forall`, `filter`, `map`, `length`/`size`, `isEmpty`/`nonEmpty`,
`++`; on `Option`: `forall`, `exists`, `contains`, `isDefined`, `isEmpty`,
`getOrElse`; params (applied or `.value`); `define`d functions.

Use `BigInt`: `Int`/`Long` arithmetic is refused, as is `exists` (or a negated
`forall`) over a type holding one. Divide only by a literal. No function-typed
fields, no types that redefine `equals`, no two `define`s with one name.

## Proving a link

1. If `check` reports a link `open`, first ask whether it is true. Usually
   the node is wrong.
2. If it is true, run `scaffold(node)`. Start with `unfold Obl.link`,
   `intro m h`, `simp only [frflow_defs] at *`. Iterate with
   `lake env lean Proofs/<KB>/<Id>.lean` in `lean/`, then run `check`.
3. A proof file holds only theorems and their tactic proofs: no `sorry`,
   `axiom`, attributes or metaprograms. It imports only
   `FrFlowGen.<KB>.Domain`, `FrFlowGen.<KB>.<Id>.Spec`, `FrFlow`, `Std`,
   `Init` and `Proofs.<KB>.Lemmas` (shared lemmas, same rules).
4. A hand-proven link also needs `feasible` (or a proven implementation below)
   and `nontrivial`; the scaffold stubs both. `vacuous_*`, `unsat` and
   `rootTrivial` reject claims that say nothing.
5. Never prove a link from a contradiction in the node, and never write a
   proof that does not use the node's spec.
