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

The developer writes the idea in `IDEA.md`. You write Scala nodes: one root, and
below it parts that together prove it, down to contracts on the code. Lean
proves each split; the developer decides every node. The README explains the
method and how to start a project, `docs/DAG.md` the design.

## Rules

1. **You propose; the developer decides.** Never edit `.frflow/ledger.json`,
   decide for the developer, create a signing key, or add files to
   `.frflow/keys/`. If `status` says decisions are not signed, tell the developer.
2. **One statement per node**, one sentence in the developer's domain words; the
   formula says exactly that sentence.
3. **A part is never a restatement.** Say what the domain adds (a concept, a
   mechanism, a rule), or attach the contract to the parent directly.
4. **2 to 5 parts per parent.** More asks for an intermediate node.
5. **The root is stated as exactly**: what users can do and what must never happen.
6. **Introduce the domain by definitions.** Leave a concept open (`Opaque`,
   `Param`) where the idea is general; fix it with a `Node.definition` where the
   domain says what it is. Below a type's definition, write parts in its
   concrete terms (a `Param` of `User.T` cannot be applied to a `UserId`).
7. **`why` carries the theory**: why this step, and what it assumes. Every
   `Opaque` and `Param` says what it means and where its value comes from.
8. **Offer real alternatives**: the second `.replaces` the first, its `why` the trade-off.
9. **Never weaken a node to make a proof go through.** A false split means a
   part is wrong or missing. If the idea or a decided node is wrong, say so.
10. **Never edit generated Lean** (`lean/FrFlowGen/`, `lean/FrFlowAudit/`). Lean
    you write goes only in `lean/Proofs/<KB>/`.
11. **Every source file is governed by one node**: an implementation, or a
    design node (production wiring, the call to `service`, goes in one).
12. **Say what is not modelled** (`## Not modelled` in `IDEA.md`), and in your
    `answer` name the waiting nodes that are mechanical.
13. **Names.** Node ids are unique identifiers, distinct from every type,
    function and term. A `Param` or `Opaque` named after a Lean word (`decide`,
    `max`, `id`, `holds`, `m`, `x0`, ...) is refused; a val named after a FrFlow
    function (`keeps`, `expect`) hides it. To rename a node, change its id and
    val, and move its proof file.
14. **Changes.** A change of formula reviews what rests on the node; a change
    to governed code reviews the node (`code`): say why its invariants still hold.

## The loop

1. `inbox`: requests, rejected nodes (who rejected each and why), the summary.
2. For each request, read `IDEA.md` and `context NODE`, and `find` where the
   change belongs. Place a new statement **under the lowest nodes it helps
   prove, as a part**. Extend what exists; do not add a near-duplicate.
3. Write the proposal with `why` and examples, add it to `KnowledgeBase(...)`,
   then `render` and `check`. Fix failing examples first, then the splits.
4. `answer REQUEST TEXT`: the proposals, the trade-off, what is left open.
5. For a rejected node: if its reason asks for something, propose a node in its
   place that does it, under the same parents. Then remove the rejected node,
   move what was under it under the node chosen, and drop its name elsewhere.
6. When the developer asks to revisit a node, propose a change, or
   `answer NODE TEXT` why it still holds.

## Tools

`bin/frflow <kb> COMMAND` from the repository root (`sbt "<kb>/run COMMAND"`
works too, slower). Piped, the output is plain ASCII and not cut; `--json` on
`tree`, `show`, `inbox`, `status` and `check` prints the typed value. `--help`
gives the rest.

| command | use |
|---|---|
| `inbox` | Start here: requests, clean-up, waiting decisions, the summary. |
| `context NODE` | Everything on a node (`show NODE --full`), nothing cut. |
| `tree [NODE]`, `show NODE`, `diff NODE` | The DAG; a node in about a screen; what changed since it was decided. |
| `find WORDS\|PATH` | The nodes that govern a file, or what mentions some words. |
| `render` | Rebuild from the Scala; compile errors and structural problems come back here. |
| `check [NODE]` | Prove what changed, evaluate the examples in Lean. Slow. A `timeout` is not a failure: run it again. |
| `status` | The tree, the summary and the warnings; exits 1 unless the knowledge base is complete. |
| `scaffold NODE` | Stubs in the node's proof file for what the last check left open. |
| `answer REQUEST\|NODE TEXT` | Reply to a request, or tell the developer of work they did not ask for. |

`ci` is `check`, then `status`. Exit codes: 0 fine; 1 not complete, or refused; 2 a usage error; 3 no Lean.

## Writing nodes

One of each kind, from the examples (`why` cut):

```scala
val User   = Opaque("User", "a person who uses the system")
val access = Param[(User.T, Resource.T) => Boolean]("access", "whether the system lets the user access the resource")
val admit  = Param[(String, Path) => Option[UserId]]("admit", "the system's decision on a request: the user it is admitted for, if any")

val accessExactly = Node.claim("AccessExactly",          // the root: the claim with no parents
  "A user gets access to a resource exactly when they are signed in and authorized for it.", why = "...")(
  forall((u: User.T, r: Resource.T) => access(u, r) == (signedIn(u) && authorized(u, r))))
val identities = Node.definition("Identities", "Users are named by ids, and resources are paths.", why = "...")(
  User := of[UserId], Resource := of[Path])
val decisionContract = Node.contract(admit)("DecisionContract",
  "A request is admitted on behalf of the user its token was issued to, exactly when a grant names that user and the path.", why = "...")(
  (token, path, decision) => decision.forall(u => sessions(token) == Some(u) && grants.value.contains(Grant(u, path))) && ...)
  .under(tokenNamesHolder, accessNeedsGrant, grantLetsIn)
  .examples(grants.bind(List(Grant(UserId("alice"), Path("/a")))), sessions.bindTable(Map("t1" -> UserId("alice"))))(
    expect("t1", Path("/a"), Some(UserId("alice")), "Alice's token and a grant for /a: she gets in"),
    reject("t1", Path("/b"), Some(UserId("alice")), "access without a grant is never given"))
val inMemorySessions = Node.design("InMemorySessions",
  "Sessions and grants are loaded into memory, in one process that decides every request.", why = "...")(
  "src/main/scala/auth/Server.scala").under(decisionContract)

val realmIsolation = Node.invariant[RealmId, Claims]("RealmIsolation",   // keycloak
  "No application is ever shown claims of a realm other than its own.", why = "...")((asking, c) => c.realm == asking)
// on the contract Introspect:   .keeps(realmIsolation)((realm, token, res) => res match { case Some(c) => List((realm, c)); case None => Nil })
// on the design ServiceWiring:  .exempt(realmIsolation, "it returns what Introspect returns, which keeps the rule")
val sessionLookup = Node.assumption(lookup)("SessionLookup",          // keycloak: a port, trusted
  "The store's index returns a session it holds under the token in the realm asked, if it holds one.", why = "...")(
  (realm, token, r) => r.forall(x => sessions(realm).contains(x) && x.token == token && x.realm == realm))
```

- **Vocabulary.** `Opaque` is a domain type (`User.T`); `Param` a fact of the
  world (`grants`) or an operation (`admit`), named as its val. A `define` is a
  function Lean translates and Scala runs.
- **Kinds.** A contract states a claim for one call of an operation, so each
  result can be checked. An assumption states what you cannot prove: a port, or
  a fact of the world (`Node.assumption(id, statement, why)(formula)`).
- **Edges.** `.under(p1, p2)`: a part of each; declare parents first (a `val`
  used before it is defined is `null`). `.keeps(inv)(view)`: the pairs a call
  shows the invariant; every contract and design node in its scope keeps it or
  is `.exempt`. `idea = "Section"`: the section of `IDEA.md` it is decided against.
- **Extras.** `.checkedBy((a, b, r) => ...)`: a cheap check of the result, run
  on every call, proven to follow from the post. `.expects(statement)(formula)`:
  a consequence the developer expects, proven from the node.
- **Examples.** Every contract needs an `expect` and a `reject`, and expects
  with different results. Bind every parameter the post reads; a lookup as
  `bindTable(Map(...))` so Lean can evaluate it. "Lean and Scala disagree"
  means the translation is wrong: report it; never change the example to hide it.
- **Implementations.** `implementProven(contract)(define {...})`: Lean proves it.
  `implementProven(c)(define {...}, (a, b) => fast)`: the fast code (an index,
  SQL; an assumption's adapter) runs, checked against the define.
  `implement(c)((a, b) => ...)`: plain code, checked by running. Code calls
  another operation through its `Param`, and is proven from its promise.
  Production calls `knowledge.service(contract)(bindings*)`, which checks every result.

## What check reports, and what to do

A try is `shown` (Lean proved it) or `not-shown` (no proof within its budget:
it shows nothing). Never write in a reason that Lean shows a part needed.

| Report | Means | Do |
|---|---|---|
| `complete` open: "automation gave up" | the parts may not make it | Usually a part is missing or too weak. If they do make it, prove it by hand. |
| `needed_C` shown | the node holds without C | C belongs elsewhere, or another part says too much. Fix the split. |
| `vacuous` shown (one part) | the node holds whatever its part says | Strengthen the node, or remove it. |
| `restates` shown (one part) | the node and its part say the same | Merge them, or say what the node adds. |
| `clash`, `unsat` shown | the parts contradict each other; no world meets the node | Fix the parts, or the node. |
| `idle` shown | doing nothing meets the root | State what users can do. |
| "nothing below proves it" | a claim with no parts | Add the parts or a contract; a fact of the world is an assumption. |
| `waiting` | two definitions not yet chosen, or parts not yet proven | Ask the developer to choose; prove the parts. |
| `impl` open | the define does not provably meet the contract | Fix the code, or prove `impl` by hand. |
| `feasible` open | an authored `complete` nothing witnesses | Prove that some world meets all the parts. |
| examples fail | the code or the contract is wrong | Fix them before any proof. |
| `ContractViolation` at run time | a result broke the contract, or a value an assumption | Fix the code or the data; never the check. |

## Proving by hand

1. `scaffold NODE` writes `lean/Proofs/<KB>/<Node>.lean`: per open obligation,
   `theorem <name> : Obl.<name>`, starting with `unfold`, `frflow_intro` and
   `simp only [frflow_defs] at *`, the goal they leave, then `sorry`.
2. `frflow_intro` names the open terms and the parts, `h_<Part>`: use the names,
   so the proof survives a part added. Iterate with
   `lake env lean Proofs/<KB>/<Node>.lean` in `lean/`, then `check`.
3. The library: `FrFlow.always`, `simulates` (`simulates_rel`,
   `simulates_of_inv`), `tracks`, `tracks_eq`, `run_snoc`, and list lemmas.
   Shared lemmas go in `lean/Proofs/<KB>/Lemmas.lean`. Lean 4.35 deprecates
   `if_pos`/`if_neg`: use `ite_eq_left`/`ite_eq_right`, or `split`.
4. A proof file holds theorems with tactic proofs only (no `sorry`, `axiom`,
   attributes or metaprograms), and imports only `FrFlowGen.<KB>.Domain`,
   `FrFlowGen.<KB>.<Node>.Spec`, `FrFlow`, `Std`, `Init`, `Proofs.<KB>.Lemmas`.
5. Never prove a split from a contradiction in the parts, or without them.

## The Scala subset

Unsupported Scala is a compile error, with the usual rewrite; or make it a `define`. Supported:
fields, case class constructors, `copy`, `match`, `if`; `==`, `!=`, `&&`, `||`,
`!`, `==>`; `forall`/`exists` over one or two typed binders; on `List`:
`contains`, `exists`, `forall`, `filter`, `filterNot`, `map`, `flatMap`,
`foldLeft`, `find`, `headOption`, `take`, `drop`, `zip`, `length`/`size`,
`isEmpty`/`nonEmpty`, `::`, `++`, `toSet`; on `Option`: `forall`, `exists`,
`contains`, `isDefined`, `isEmpty`, `getOrElse`; on `Map`: `get`, `getOrElse`,
`contains`, `updated`, `removed`, `+`, `-`, `==`, `Map(k -> v)`, `Map.empty`
(not `m(k)`); on `Set`: `contains`, `+`, `-`, `++`, `intersect`, `subsetOf`, `Set(...)`.
Maps and sets cannot be iterated. Use `BigInt` (`+`, `-`, `*`, `max`, `min`,
comparisons, `/` and `%` by a literal): `Int`/`Long` arithmetic is refused. No
function-typed fields, no types that redefine `equals`, no two `define`s with one name.
