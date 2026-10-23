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
  `Node.invariant`, `.under`, `.replaces`, `implementProven` or `service`;
  or terms (`Term`, `define`, `Data`), flows (`Flow`), boundaries
  (`Boundary`) or state models (`StateModel`).
---

# Developing with FrFlow

The developer tells you the idea in chat; you ask what you need, record the
conversation, and write `IDEA.md` from it for them to accept. Then you write
Scala nodes: one root, and below it parts that together prove it, down to
contracts on the code. Lean proves each split; the developer decides every node,
and `IDEA.md`. The README explains the method, `docs/DAG.md` the design.

## Starting a project: the conversation

1. **Set up.** `sbt "frflowInit NAME"` (a lowercase name), then `sbt reload`:
   an empty knowledge base in `examples/NAME`. `bin/frflow NAME status` works
   from here.
2. **Let the developer tell the idea**, in their own words, as long or short
   as they like. Record it verbatim: `said TEXT` (each message that tells the
   idea or corrects it). Do not write files yet.
3. **Ask, 3 to 5 questions at a time**, each with the answer you assume, so
   the developer can just agree or correct it: "Can a company share a record
   with another? I assume yes, only the owner can, until a date." Ask what
   decides the root and the first split: who the users are, what they can do,
   what must never happen, what the system keeps, what is out of scope. Record
   each before asking it: `asked QUESTION --assume ANSWER` gives `Q1`, `Q2`, ...;
   record each answer as said: `replied Q TEXT`. Stop when the root can be
   stated; ask later questions when a node needs them, the same way.
4. **Restate the purpose in one sentence** ("A user finds exactly ...") and
   ask the developer to confirm or correct it in chat. It becomes the root.
5. **Write `IDEA.md`** from the conversation, in the developer's words where
   possible: a title, a lead paragraph (the purpose), `## ` sections (one per
   concern: what users do, what must never happen, what is kept), and
   `## Not modelled` (what they said is out of scope). Under each heading, a
   line `From: Q1, Q3` names the answers it comes from. Never put in it
   anything the developer did not say or agree to.
6. **Ask the developer to accept it**: `accept IDEA` on their terminal, or in
   the web view (you cannot: it is signed). `inbox` shows it waiting. If they
   want changes, edit it and ask again.
7. **Then propose the root and the first parts**, each naming its section
   (`idea = "..."`) and, in its `why`, the answers it rests on. Where a node
   needs something the developer has not said, ask (step 3) instead of
   guessing.

`conversation` shows what is recorded. A reply that changes an answer after
`IDEA.md` was accepted is a warning in `status`: update the sections that name
it, and ask the developer to accept `IDEA.md` again; the nodes naming a changed
section come back to them.

## Rules

1. **You propose; the developer decides.** Never edit `.frflow/ledger.json`,
   decide for the developer (`IDEA.md` included), create a signing key, or add files to
   `.frflow/keys/`. Record the conversation only as it happened: never a reply
   the developer did not give. If `status` says decisions are not signed, tell the developer.
2. **One statement per node**, one sentence in the developer's domain words; the
   formula says exactly that sentence.
3. **A part is never a restatement.** Say what the domain adds (a concept, a
   mechanism, a rule), or attach the contract to the parent directly. A node
   whose only job is to rename terms is a definition, or folds into its parent.
4. **2 to 5 parts per parent, as a rule.** More asks for an intermediate node.
5. **The root is stated as exactly**: what users can do and what must never
   happen, as one relation (`===`, "exactly when") between what users observe and
   what their requests entitle them to, defined over the history of requests
   when the purpose has one. A part proves that the state mirrors the history
   (keycloak's `SessionsMirrorSignIns`). A conjunction at the root asks for a
   better observable.
6. **The first split is ⇒/⇐** (safety and capability) **or state/reads**, not
   one part per conjunct. The top nodes each name their `IDEA.md` section.
7. **Introduce the domain by definitions.** Leave a concept open (`Opaque`,
   `Param`) where the idea is general; fix it with a `Node.definition` where the
   domain says what it is. Below a type's definition, write parts in its
   concrete terms (a `Param` of `User.T` cannot be applied to a `UserId`).
8. **`why` carries the theory**: why this step, and what it assumes. Every
   `Opaque` and `Param` says what it means and where its value comes from.
9. **Offer real alternatives**: the second `.replaces` the first, its `why` the trade-off.
10. **Never weaken a node to make a proof go through.** A false split means a
    part is wrong or missing. If the idea or a decided node is wrong, say so.
11. **Never edit generated Lean** (`lean/FrFlowGen/`, `lean/FrFlowAudit/`). Lean
    you write goes only in `lean/Proofs/<KB>/`.
12. **Every source file is governed by one node**: an implementation, or a
    design node (production wiring, the call to `service`, goes in one).
13. **Say what is not modelled** (`## Not modelled` in `IDEA.md`), and in your
    `answer` name the waiting nodes that are mechanical.
14. **Names.** Node ids are unique identifiers, distinct from every type,
    function and term. A `Param` or `Opaque` named after a Lean word (`decide`,
    `max`, `id`, `holds`, `m`, `x0`, ...) is refused; a val named after a FrFlow
    function (`keeps`, `expect`) hides it. To rename a node, change its id and
    val, and move its proof file.
15. **Changes.** A change of formula reviews what rests on the node; a change
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
| `inbox` | Start here: requests, clean-up, waiting decisions (`IDEA.md` first), open questions, the summary. |
| `said TEXT`, `asked QUESTION --assume ANSWER`, `replied Q TEXT`, `conversation` | Record the conversation the idea comes from; show it. |
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
val admit  = Param[(String, Path) => Option[UserId]]("admit", "the system's decision on a request (a token and a path): the user it is admitted on behalf of, if any")

val accessExactly = Node.claim("AccessExactly",          // the root: the claim with no parents
  "A user gets access to a resource exactly when they are signed in and authorized for it.", why = "..."
)(forall((u: Term[User.T], r: Term[Resource.T]) => access(u, r) === (signedIn(u) && authorized(u, r))))
val identities = Node.definition("Identities", "Users are named by ids, and resources are paths.", why = "..."
)(User := of[UserId], Resource := of[Path])
val decisionContract = Node.contract(admit)("DecisionContract",
  "A request is admitted on behalf of the user its token was issued to, exactly when a grant names that user and the path.", why = "..."
)((token, path, decision) => decision.forall(u => sessions(token) === Some(u) && grants.contains(Grant(u, path))) && ...)
  .under(tokenNamesHolder, accessNeedsGrant, grantLetsIn)
  .examples(grants.bind(List(Grant(UserId("alice"), Path("/a")))), sessions.bindTable(Map("t1" -> UserId("alice"))))(
    expect("t1", Path("/a"), Some(UserId("alice")), "Alice's token and a grant for /a: she gets in"),
    reject("t1", Path("/b"), Some(UserId("alice")), "access without a grant is never given"))
val admitted = define { (token: Term[String], path: Term[Path]) =>     // code Lean proves
  sessions(token)
    .on[Some[UserId]](u => If(grants.contains(Grant(u, path)))(some(u)).Else(none))
    .on[None.type](none)
}
val inMemorySessions = Node.design("InMemorySessions",
  "Sessions and grants are loaded into memory, in one process that decides every request.", why = "..."
)("src/main/scala/auth/Server.scala").under(decisionContract)

val realmIsolation = Node.invariant[RealmId, Claims]("RealmIsolation",   // keycloak
  "No application is ever shown claims of a realm other than its own.", why = "..."
)((asking, c) => c.realm === asking)
// on the contract Introspect:  .keeps(realmIsolation)((realm, token, res) => res.on[Some[Claims]](c => List((realm, c))).on[None.type](Nil))
// on the design ServiceWiring: .exempt(realmIsolation, "it returns what Introspect returns, which keeps the rule")
val sessionLookup = Node.assumption(lookup)("SessionLookup",          // keycloak: trusted
  "The store's index returns a session it holds under the token in the realm asked, if it holds one, and never one of another realm or token.", why = "..."
)((realm, token, r) => r.forall(x => sessions(realm).contains(x) && x.token === token && x.realm === realm) && ...)
```

- **Vocabulary.** `Opaque` is a domain type (`User.T`); `Param` a fact of the
  world (`grants`) or an operation (`admit`), named as its val, and itself a
  term (`grants.contains(g)`, `sessions(t)`). A `define` is a named function
  over terms: Lean's `def` of the same name, and Scala runs it.
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
  means FrFlow's Lean printer or evaluator is wrong: report it; never change
  the example to hide it.
- **Implementations.** `implementProven(contract)(define {...})`: Lean proves it.
  `implementProven(c)(define {...}, (a, b) => fast)`: the fast code (an index,
  SQL; an assumption's adapter) runs, checked against the define.
  `implement(c)((a, b) => ...)`: plain code, checked by running. Code calls
  another operation through its `Param`, and is proven from its promise.
  Production calls `knowledge.service(contract)(bindings*)`, which checks every result.

## Writing terms

Formulas and proven code are terms (`Term[A]`), built from the library's
operations; there is no macro, so what is not offered is a type error.

- **Annotate lambda parameters** as terms: `(s: Term[CrmStore], now: Term[BigInt]) => ...`.
  Quantifiers too: `forall((u: Term[User.T]) => ...)`, `exists(...)`, one or two variables.
- **`===` and `=!=`**, never `==` (between terms it does not compile). `&&`,
  `||`, `!`, `==>`; `True` and `False` for the constants.
- **Build data from terms through its companion**: `object CrmStore extends Data[CrmStore]`
  makes `CrmStore(a, b, c)` a term (1 to 6 fields); `object Event extends Data[Event]`
  makes `Event[Event.Expired](now)` a term of the enum. Copy with a named tuple:
  `a.copy((enabled = v))`. Fields read as on values: `s.records`.
- **Matches** are `.on[Case](fields => ...)` per case, in order: `q.on[Search.ById](id => ...)`;
  a singleton case is `.on[Search.Everything.type](...)`; an option `.on[Some[A]](x => ...).on[None.type](...)`.
  Missing cases fail when the Lean is rendered.
- **`If(c)(a).Else(b)`**; `let(v)(x => ...)` names a shared value; `some(x)`, `none[A]`.
- **In plain Scala** (implementations, wiring, tests): call a define with `d.fn(...)`
  and read a parameter with `p.value`.
- Operations: on `List`: `contains`, `exists`, `forall`, `filter`, `filterNot`,
  `map`, `flatMap`, `foldLeft`, `find`, `headOption`, `take`, `drop`, `zip`,
  `length`/`size`, `isEmpty`/`nonEmpty`, `::`, `++`, `toSet`; on `Option`:
  `forall`, `exists`, `contains`, `isDefined`, `isEmpty`, `getOrElse`; on `Map`:
  `get`, `getOrElse`, `contains`, `updated`, `removed`, `+`, `-`; on `Set`:
  `contains`, `+`, `-`, `++`, `intersect`, `subsetOf`. Maps and sets cannot be
  iterated. Arithmetic on `BigInt` (`+`, `-`, `*`, `max`, `min`, comparisons,
  `/` and `%` by a literal); `Int` and `Long` only compare. Tuples up to three.
  No function-typed fields, no types that redefine `equals`, no two `define`s
  with one name.

## Effectful code: boundaries, models and flows

Use a flow when code takes several steps against the outside (load, store,
log): its order and its loop are then proven, not only reviewed. A single
call whose result is checked stays an assumption on an operation.

```scala
trait Database:                                       // the boundary: what proven code may ask
  def load: Flow[CrmStore]
  def storeAbout(id: Term[BigInt], t: Term[CrmStore]): Flow[Unit]
  def logEvent(e: Term[Event]): Flow[Unit]
val db = Boundary[Database]("database", "the SQLite database the CRM keeps its records, shares, expiries and event log in")

object DatabaseModel extends Database, StateModel[Tables]:   // what it does, as the proofs see it
  def load = state.get.map(t => t.store)
  def storeAbout(id: Term[BigInt], s: Term[CrmStore]) = state.update(t => Tables(replaceAbout(t.store, id, aboutRecord(s, id)), t.events))
  def logEvent(e: Term[Event]) = state.update(t => Tables(t.store, t.events ++ List(e)))
val tablesModel = Node.assumption(db)(DatabaseModel)("TablesModel", "...", why = "...")
  .checkedAgainst(t => SqliteDatabase.holding(t), _.tables)

def expireOnce(now: Term[BigInt]): Flow[CrmStore] =   // the code: a plain def, Cats-style
  for
    s <- db.load
    t  = expire(s, now)
    _ <- changedIds(s, t).traverse_(id => db.storeAbout(id, t))
    _ <- db.logEvent(Event[Event.Expired](now))
  yield t
// the contract, on runExpiry: Param[BigInt => Flow[CrmStore]]:
//   Node.contract(runExpiry)("ExpiryJob", "...", why = "...")((now, result, before, after) =>
//     sameRows(after(DatabaseModel).store, expire(before(DatabaseModel).store, now)) && ...)
// knowledge.implementProven(expiryJob)(expireOnce); production: knowledge.run[SyncIO](expiryJob)(db.bind(SqliteDatabase(d)))(now)
```

- **The model is a decision.** State it in the domain's words; it is trusted.
  It must be deterministic (put unknowns, such as clock readings, into the
  state), never failing, and the flow's alone during a run: a design node says
  how that is ensured (a lock, a transaction). Loops are over lists
  (`traverse_`). Give `.checkedAgainst` so the production implementation is
  run beside the model on the examples.
- **Steps.** `state.get`, `state.set(s)`, `state.update(f)` in models only;
  `Flow.effect(...)` in production implementations only (a proven flow taking
  one is refused); `If(c)(f1).Else(f2)` and `Flow.when(c)(f)` for branches.
- **The contract's examples** give the world before and after:
  `expect(BigInt(150), World(DatabaseModel -> Tables(...)), result, World(DatabaseModel -> Tables(...)), "...")`.
- **Calling an operation from a flow** (`expire` above) proves the flow from
  that operation's contract, not its code: prefer it to calling the define.
- A contract on a flow may have no parent: production runs it, as an entry
  point. The design node over its scheduling goes under it.

## What check reports, and what to do

A try is `shown` (Lean proved it) or `not-shown` (no proof within its budget:
it shows nothing). Never write in a reason that Lean shows a part needed.

| Report | Means | Do |
|---|---|---|
| `complete` open: "automation gave up" | the parts may not make it | Usually a part is missing or too weak. If they do make it, prove it by hand. |
| `needed_C` shown | the node holds without C | C belongs elsewhere, or another part says too much. Fix the split. |
| `vacuous` shown (one part) | the node holds whatever its part says | Strengthen the node, or remove it. |
| `restates` shown (one part) | the node and its part say the same | Merge them, or say what the node adds. |
| `restates_<i>_<P>` shown | part P says what conjunct i of the node says, with the definitions applied | Fold P into the node, or say what P adds; better, restate the node as one relation. |
| `clash`, `unsat` shown | the parts contradict each other; no world meets the node | Fix the parts, or the node. |
| `idle` shown | doing nothing meets the root | State what users can do. |
| "nothing below proves it" | a claim with no parts | Add the parts or a contract; a fact of the world is an assumption. |
| `waiting` | two definitions not yet chosen, or parts not yet proven | Ask the developer to choose; prove the parts. |
| `impl` open | the define or flow does not provably meet the contract | Fix the code, or prove `impl` by hand. |
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
6. **A flow's `impl`.** Run it on the models with
   `simp only [<Node>.post, f_run, f, FrFlow.runOn_bind, FrFlow.runOn_pure, FrFlow.runOn_within,
   FrFlow.runOn_get, FrFlow.runOn_modify, FrFlow.runOn_forIn_unit, <B>.<op>_onWorld, <Model>.<op>]`,
   keeping the domain's definitions folded. `runOn_forIn_unit` turns a loop
   into a `List.foldl` over worlds: prove what the fold does by induction on
   the list, in lemmas of your own (see `examples/crm/lean/Proofs/Crm/ExpiryJob.lean`).
