---
name: frflow
description: Develop a system with FrFlow, where the developer decides, in a browser, a tree of Scala nodes, each proven in Lean to refine its parent, that keeps the theory of the system (what holds, why, and what was rejected) and shows when code or design drifts from it. Use when turning an idea into a root, proposing or changing nodes (refine, instantiate, contract, design, invariant), adding examples, answering the developer's requests, proving a link, or attaching an implementation. Also use when the work touches IDEA.md, frflow.json, `Node.root`, `.refine`, `.instantiate`, `.contract`, `.design`, `Node.invariant`, `.keeps`, `.exempt`, `.examples`, `.implement`, `.implementProven`, `.implementChecked`, `.governing`, `.relies`, `.reliesThat` or `service`.
---

# Developing with FrFlow

FrFlow keeps the theory of a system: what it must do, and why it is designed
this way. It also keeps the code from drifting away from it.

- The developer writes the idea in `IDEA.md`.
- The **tree** under each root specializes one concern of the idea step by
  step; invariants cut across the trees. Each node is a Scala val with a
  statement, a reason (`why`), and a formal model. Contracts also have
  examples.
- **The developer decides every node in the browser.** You propose. They
  choose, and their reason is kept along with the alternatives they rejected.
- A decision is bound to what was decided. If the node changes, the meaning of
  something above it changes, or the code it governs changes, the node goes
  back to **review** and the browser asks the developer again, showing what
  moved. This is how drift shows.
- Lean proves each node implies its parent, so the idea holds all the way
  down.
- Examples check that the contract and the implementation do what was decided.

## Rules

1. **You propose; the developer decides every node.**
   - You never write the ledger. There is no tool or command for deciding. Do
     not post to the browser's server, and do not edit `.frflow/ledger.json`:
     a decision without the developer's signature fails `status`, and so
     does rewriting committed decisions.
   - Never run `frflow serve`, create a signing key, or add files to
     `.frflow/keys/`: the first key committed is the developer key. If
     `status` says "no developer key", tell the developer to start the
     browser, commit `.frflow/keys/` and sign there.
   - Mechanical decisions (no choice in them, Lean proves them again; see the
     README's "Who decides") are the developer's too: the browser offers them
     in one batch. In your `answer`, say which waiting nodes are mechanical.
   - A decision below a change whose reason or `why` says when to revisit it
     ("revisit if", "unless", "until"...) is answered by the developer by
     name. In your `answer`, say whether each such condition may be met.
2. **Offer real alternatives.** When a step has more than one reasonable
   design, propose each as a sibling node, with its own `why` covering its
   trade-off. One proposal is fine when the step is obvious.
3. **`why` carries the theory.** Say why this step, and what it assumes about
   the world.
   - For `refine`, say why `abs` is a faithful mapping.
   - For `instantiate`, say why the substitutions are the right meanings in
     the world.
   - A reader must be able to tell a deliberate choice from an accident.
4. **The statement must say in plain words what the predicate says.**
5. **Every contract gets examples** (the build requires it).
   - Expects with different results, so an implementation that always
     returns the same value fails one of them (the build requires it).
   - At least one `reject` showing what is ruled out.
   - Read the contract's "does not promise" list, and say in your answer what
     it means for the developer.
   - Examples are how the developer checks that a predicate means what its
     statement says.
6. **Every `Opaque` and `Param` says what it means in the world**, and where a
   parameter's value comes from. For example:
   `Param[List[Grant]]("grants", "the grant table as stored when the request is decided")`.
   That is the vocabulary of the theory.
7. **Record design decisions that have no formal model as `design` nodes.**
   Prefer a formal node where the subset can say it: the proven chain is the
   point.
   Storage, caching, conventions and the like go in a `design` node, with its
   `why` and the files it governs.
8. **The model is the Scala code.**
   - Never edit `lean/FrFlowGen/` or `lean/FrFlowAudit/`.
   - Lean you write goes only in `lean/Proofs/<KB>/<NODE>.lean`.
9. **Never weaken a node to make a proof go through.** A false link means the
   child is wrong. If you think the idea or a decided node is wrong, say so in
   your answer and propose a change.
10. **Keep the tree honest about its limits.** When part of the idea is not
   modelled, propose adding it to the `## Not modelled` section of `IDEA.md`.

## The loop

1. **`inbox`.** It shows:
   - the developer's open requests;
   - rejected nodes you must delete from the Scala model;
   - decisions still waiting for the developer (mechanical ones marked);
   - the tree.
2. **For each request,** read `context(node)`, and `find` where the change
   belongs: extend the nodes that already cover it rather than adding a
   near-duplicate. Then write the proposals as Scala nodes, with `why` and
   examples. Add them to the `KnowledgeBase(...)` list.
3. **`render`, then `check`.** Fix compile errors and links that do not hold.
   Proposals should reach the developer proven, with passing examples.
   `check` lists failing examples first: the code or the contract is wrong;
   fix that, not the proof. Then what is not proven besides the link.
4. **`answer(request, text)`.** Name the proposals, the trade-off between them,
   and anything left open. For example: "Proposed Expiring and Sliding under
   Authenticated. Expiring is simpler; Sliding keeps active users signed in.
   Choose in the browser."
5. **After the developer decides,** delete the rejected nodes from the Scala
   code (`status` fails while they remain). If a rejected node had nodes below
   it, move them under the node chosen instead: they are reviewed again. Their statements and reasons are kept with the decision. Then
   `render`.
6. **If you change an accepted node,** it goes back to `review` (cause
   `self`), with a diff. If its meaning changed, its descendants go to
   `review` too (cause `above`); rewording a `why` or adding an example does
   not reach them. Explain the change in an answer or in the node's `why`.
   - **Replacing an accepted node:** propose the new node as its sibling. The
     developer can reject the old one when choosing.
   - **A change to an implementation or a governed file** puts the node up for
     review (cause `code`), with a git diff, and no proof covers it: make
     sure the examples still pass, and say what changed in your answer. The
     review notes the invariants whose domain types the diff names and the
     parameters it binds anew: say in your answer why each still holds.
     An implementation governs the files its expression refers to. Code it
     relies on elsewhere needs an owner: `.governing(paths*)`, or a design
     node owning a directory. `status` fails on a source file no node governs:
     anything under `src/main`, any source file elsewhere in the project (not
     `src/test`; `target` folders in the sources, `project/*.scala` and
     `*.sbt` count), and anything the build compiles (keep the build passing
     `-Dfrflow.sources`). Never declare `package frflow` in the project.
   - **A rule that applies to several contracts** (tenant isolation,
     authorization, auditing) is an **invariant**, stated once over pairs:
     `Node.invariant[Account, CrmRecord](id, statement, why)((reader, r) => ...)`.
     Declare it before the contracts. Every contract in its `scope` (all by
     default) either keeps it, listing the pairs a call shows the rule,
     `.keeps(inv)((user, query, result) => result.map(r => (user, r)))`, or
     says why it does not apply, `.exempt(inv, "it returns no records")`.
     Every design node in its scope says why too (`.exempt`): it governs code
     no proof covers.
     A view lists every pair the result shows: for a rule about a domain or
     opaque type, Lean proves it lists every such value the result holds,
     with the caller (`cover_X`). When several inputs have the rule's first
     type, name the one the pairs are about: `.keeps(inv, reader = 1)(...)`
     (from 0); otherwise `cover_X` fails. A view that leaves something out,
     however the filter is hidden, fails; so does one that keeps the rule in
     name only (`vacuous_inv_X`).
   - **Keep production wiring** (the call to `service`) in a file a design
     node governs. Every change to it is the developer's.
   - **Prefer a proven implementation.** When the implementation fits the
     Scala subset, write it as a `define` and register it with
     `implementProven(contract)(impl)`: Lean proves it meets the contract, and
     the chain reaches the code. When the code must be faster than the
     subset allows, keep the `define` as its oracle:
     `implementChecked(contract)(fast)(define)`: the fast code runs and must
     return what the `define` returns on every example and every combination
     of their inputs. It is not proven code (nor counted as such), and a
     change to it is never mechanical. If IDEA.md says `Proven code: N%`,
     `status` fails while fewer contracts are proven down to the code that
     runs; the line is the developer's (part of the idea), never lower it.
   - **Name the idea's section** a root is decided against
     (`Node.root(..., idea = "Sharing")`) when `IDEA.md` has `## ` sections,
     so editing one section reviews only its root. What only one concern
     leaves out goes in a `### Sharing` subsection of `## Not modelled`.
   - **When a node depends on what another node says** outside its path
     (often another concern: the read side on what every write keeps),
     declare it: `.relies(crmWrites, "ids are unique in every store writes
     reach")`. `context` lists other concerns calling the same definitions:
     check whether you rely on them. A change to the relied node's meaning
     then reviews yours. A reliance that leads back to the node is refused.
     A property of the parameters you rely on is stated with a definition
     the relied node (or one above it) uses, so it is what is proven there:
     `.reliesThat(crmWrites, why)(() => consistentStore(CrmStore(store.value, shares.value)))`.
     Every example and `service` call checks it.
   - **The model's file holds only the model:** nodes, `Opaque`, `Param`,
     `define`, domain types without methods, and the `@main`. Helpers go next
     to the implementation; `status` warns otherwise.
   - **When the developer asks you to revisit a node** (the inbox says so), propose
     a change, or `answer` with `node` why it still holds (that answers their
     open request on the node).
   - **When you change the idea or what is not modelled,** say in your answer
     which decisions below rest on it (their reasons say), so the developer
     can tick them for revisiting.
   - **Formal work on several alternatives** can be expensive. You may first
     describe the options in your `answer`, and formalize the one the developer
     picks.

## Tools

The MCP server `frflow` (`bin/frflow mcp examples`, see `.mcp.json`) works on every project under
`examples/`. Pass `project` when there is more than one.

| tool | use |
|---|---|
| `inbox` | Start here: requests, clean-up, waiting decisions, and the tree. |
| `context(node)` | What bears on the node: its root's idea section (with its Not modelled), the vocabulary its path and reliances use, the roots in one line, the path from the root with each node's latest binding reason first, then every accepted change to it, newest first (marked "[given for an earlier version of it]" when the node changed since), then confirmations briefly, what stands beside it and what was rejected there with the reasons, what it relies on and what relies on it, other concerns calling the same definitions, invariants, what moved (with diffs, including nodes its ancestors rely on; a code diff with notes on invariants and parameters it touches), the decisions below, the obligation, the last check's failures with Lean's full message, and the developer's requests. |
| `render` | Rebuild from the Scala definitions; the browser updates. Compile errors in the model come back here. |
| `check(node?)` | Prove what changed in Lean, and evaluate the examples there. Prints Lean's full message for what fails, once. Slow. |
| `answer(request, text)` | Reply to a request; the reply is shown in the browser. With `node` and no `request`, it answers the developer's open request on that node, or tells them about work they did not ask for. |
| `find(query)` | Which nodes govern a file; or what mentions a concern, best first, with the matching sentence: nodes and all their reasons, rejected options (also those removed from the model), gone nodes, lines of Not modelled. Where a change belongs, and what was already rejected. |
| `scaffold(node)` | Stubs, in the node's proof file (created or added to), for exactly the obligations the last check left open; before any check, the link with `feasible` and `nontrivial`. |

Without MCP, use the CLI from the repository root: `sbt "auth/run render"`,
`check [NODE]`, `status`, `context NODE`, `scaffold NODE`. `ci` is what CI
runs (everything proven afresh, then `status`); you do not need it.

## Writing nodes

```scala
val authenticated = noUnauthorizedAccess.refine[(Token.T, Resource.T) => Option[User.T]](
  "Authenticated",
  "A request is granted on behalf of a user only if its token belongs to that user and the user is authorized.",
  why = "Users identify themselves with tokens they receive at login, so a decision sees a token, not a user. " +
        "abs: a user is allowed a resource when some token of theirs is granted it."
)(
  abs  = decide => (u, r) => exists((t: Token.T) => decide(t, r) == Some(u)),
  spec = decide => forall((t: Token.T, r: Resource.T) => decide(t, r).forall(u => holder(t) == Some(u) && authorized(u, r))))
```

**`Node.root(id, statement, why, idea = "Section")(spec)`** states one concern of the idea over
generic types. It may have several roots, one per concern. Make every concept
the idea does not define generic: `Opaque` for types, `Param` for relations and
values.

**`refine(id, statement, why)(abs, spec)`** is a more concrete model. Its
obligation is `spec m → parent.spec (abs m)`.

**`instantiate(id, statement, why)(T := of[X], p := expr)`** fixes opaque
types and parameters. Its link holds by substitution, so you prove nothing;
Lean checks it builds (`status`: link proven (instantiation)).

**`contract(id, statement, why)(post)`** is for a model `(A, B) => R`. `post`
must hold for every call. **`contractVia(id, statement, why)(abs)(post)`** is a
contract with a signature of its own: `abs` says what an implementation is as
the parent's model. Say what a call must do, not only what it must not: a
contract that doing nothing meets is listed as such.

**`expects(statement)(m => ...)`** states a consequence the developer expects of
every model of a node, proven from its spec. Propose some when a node is new:
they let the developer test their understanding.

**`assume = true`** (on `refine`, `contract`, `contractVia`) keeps the node's spec in Lean but
assumes its link instead of proving it: the developer decides it by reading,
and every root theorem resting on it names the assumption. Prefer it to
`formal = false` when only the proof is the problem.

**`formal = false`** (on `Node.root`, `refine`, `instantiate`, `contract`)
opts a node out of Lean. Its model stays Scala and may use any Scala; a
contract still runs its examples and `service` still checks it. Its link is
decided by reading, and everything below it is out of Lean too. Formal is the
default: opt out only when a proof costs more than it gives, or the subset
cannot express it (state, time, effects), and say so in `why`.

**`design(id, statement, why)(files*)`** is a decision with no formal model.
It has nothing to prove, and its files are tracked for change.

**`.relies(node, why)`** (on any node) says it rests on what `node` says, as
on its parent. `node` is named by its val and may be declared later.

**Examples:** Lean evaluates each example whose parameters are values (not
functions) and must compute what Scala does. "Lean and Scala disagree" means
the translation does not mean what the Scala does: report it to the developer;
never change the example to hide it.

```scala
  .examples(grants.bind(List(Grant(alice, Path("/a")))), sessions.bind(Map("t1" -> alice).get))(
    expect("t1", Path("/a"), Some(alice), "Alice's token and a grant for /a: she gets in"),
    reject("t1", Path("/b"), Some(alice), "access without a grant is never given"))
```

**The implementation** is plain Scala, preferably in its own file.
- Register it once:
  `KnowledgeBase(...)(...).implement(contract)(MyImpl(grants.value.toSet, sessions.value).decide)`
  - The examples run against it.
  - A change to its source file shows on the contract.
- Production uses the same registration:
  `knowledge.service(contract)(grants.bind(...), ...)`. Each result is checked
  against the contract; one that breaks it raises `ContractViolation`.
- **A write is a contract that returns a change, not the new state.** For
  example, `(Account, Share) => Change` with `enum Change { case AddShare(s); case Denied }`.
- In a contract, the facts that decide access (ownership, identity) must come
  from bound parameters over the system's own data, never from fields of the
  result. The implementation controls the result.

## The Scala subset in node lambdas

Unsupported Scala is a compile error `FrFlow: not supported in a model`. When
you hit one, rewrite the expression, or make the function a `define { ... }`.

The macro supports:
- fields, case class constructors, `copy`, `match` and `if`;
- `==` and `!=`;
- `&&`, `||` and `!`;
- integer `+ - * / %`, comparisons, and `min`/`max` on `Int`;
- `==>`, `forall(...)` and `exists(...)` over one or two typed binders;
- on `List`: `contains`, `exists`, `forall`, `filter`, `map`, `length`/`size`,
  `isEmpty`/`nonEmpty` and `++`;
- on `Option`: `forall`, `exists`, `contains`, `isDefined`, `isEmpty` and
  `getOrElse`;
- params, applied or as `.value`;
- `define`d functions.

Arithmetic is on `BigInt` (exact in Scala and in Lean); `+ - *` on `Int` or
`Long` is refused, since Scala wraps around; so is `exists` over a type holding
an `Int` or `Long` however deep, or fixing to such a type an opaque type said
to exist above (Lean may find a value Scala cannot hold). Use `BigInt`. A
`forall` over `Int` or `Long` left of `==>` ranges over more in Lean. Divide
only by a literal. Fields of domain types are data: a field of function type
is refused, as is a type redefining `equals`, `hashCode` or `canEqual`.

**State.** Model a stateful part as a step `(State, Event) => State` whose root
says an invariant holds initially and every step keeps it
(`inv(initial.value) && forall((s, e) => inv(s) ==> inv(step(s, e)))`);
`FrFlow.always` gives it for every reachable state. See the CRM's writes.

## Proving a link

1. If `check` reports a link `open` with "frflow_auto found no proof", first
   ask whether the obligation is true. Usually it is not, and the node is
   wrong.
2. If it is true, run `scaffold(node)` and prove `theorem link : Obl.link` in
   the proof file (it stubs each obligation the last check left open). Start
   with `unfold Obl.link`, then `intro m h`, then `simp only [frflow_defs] at *`.
3. The file may contain only theorems and their tactic proofs. Anything else
   is rejected: `sorry`, `axiom`, `run_cmd`, `#eval`, attributes, and so on.
   It may import only `FrFlowGen.<KB>.Domain`, `FrFlowGen.<KB>.<Node>.Spec`,
   `FrFlow`, `Std`, `Init` and `Proofs.<KB>.Lemmas`: never a node's Theorems
   or Auto module (Auto holds an assumed link's axiom). Accepted proofs are
   replayed through the Lean kernel, and their axioms audited: an assumed
   link's axiom may stand only under `root` and `root_impl`. Lemmas several
   proofs use go in `lean/Proofs/<KB>/Lemmas.lean` (same rules).
4. An authored link also needs `theorem feasible : Obl.feasible` (some model
   meets the node), unless a proven implementation at or below it is one
   (its `root_impl` proven, through no assumed link), and `theorem
   nontrivial : Obl.nontrivial` (some model fails the root under the meanings
   fixed so far; see the CRM's `StepByStep`). The scaffold stubs both; until
   they are proven, the link shows open. `check` also rejects a claim that
   says nothing when `frflow_auto` shows it (`vacuous_*`, `unsat`,
   `rootTrivial`), and lists as a limit a clause of the root the meanings
   above decide (`clause_i`): say so in your answer. Never write a proof that
   does not use the node's spec.
5. **Never prove a link from a contradiction in the node** (for example by
   deriving `False` from its spec). The automatic unsatisfiability check does
   not catch every contradiction, and a change to a proof file reviews no
   decision (the kernel replays it, and `feasible` and `nontrivial` must hold).
