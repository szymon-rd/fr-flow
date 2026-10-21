---
name: frflow
description: Develop a system with FrFlow, where the developer decides, in a browser, a tree of Scala nodes that keeps the theory of the system (what holds, why, and what was rejected) and shows when code or design drifts from it. Use when turning an idea into a root, proposing or changing nodes (refine, instantiate, contract, design), adding examples, answering the developer's requests, proving a link, or attaching an implementation. Also use when the work touches IDEA.md, frflow.json, `Node.root`, `.refine`, `.instantiate`, `.contract`, `.design`, `.examples`, `.implement`, `.governing` or `service`.
---

# Developing with FrFlow

FrFlow keeps the theory of a system: what it must do, and why it is designed
this way. It also keeps the code from drifting away from it.

- The developer writes the idea in `IDEA.md`.
- The **tree** specializes the idea step by step. Each node is a Scala val with
  a statement, a reason (`why`), and a formal model. Contracts also have
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

1. **You propose; the developer decides.**
   - Never accept nodes. There is no tool for it. Do not run `accept` from a
     shell, and do not edit `.frflow/ledger.json`. Rewriting committed
     decisions shows as a warning.
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
   - decisions still waiting for the developer;
   - the tree.
2. **For each request,** read `context(node)`. Then write the proposals as
   Scala nodes, with `why` and examples. Add them to the `KnowledgeBase(...)`
   list.
3. **`render`, then `check`.** Fix compile errors and links that do not hold.
   Proposals should reach the developer proven, with passing examples.
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
     review (cause `code`), with a git diff. Make sure the examples still pass.
     An implementation governs its package directory and everything below it.
     Use `.governing(paths*)` for anything else it depends on. `status` warns
     about source files no node governs: govern them, or say why not.
   - **Keep production wiring** (the call to `service`) in a file a design
     node or the implementation governs, so a change to it is reviewed.
   - **The model's file holds only the model:** nodes, `Opaque`, `Param`,
     `define`, domain types without methods, and the `@main`. Helpers go next
     to the implementation; `status` warns otherwise.
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
| `context(node)` | The idea, the vocabulary, the roots, the path from the root with every decision, reason and rejected alternative, what moved since the node was decided (with the code diff), the decisions directly below, examples, the obligation, and the developer's requests. |
| `render` | Rebuild from the Scala definitions; the browser updates. Compile errors in the model come back here. |
| `check(node?)` | Prove the links that changed in Lean. Slow. |
| `answer(request, text)` | Reply to a request; the reply is shown in the browser. |
| `scaffold(node)` | A proof file for an obligation `frflow_auto` did not prove. |

Without MCP, use the CLI from the repository root: `sbt "auth/run render"`,
`check [NODE]`, `status`, `context NODE`, `scaffold NODE`.

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

**`Node.root(id, statement, why)(spec)`** states one concern of the idea over
generic types. It may have several roots, one per concern. Make every concept
the idea does not define generic: `Opaque` for types, `Param` for relations and
values.

**`refine(id, statement, why)(abs, spec)`** is a more concrete model. Its
obligation is `spec m → parent.spec (abs m)`.

**`instantiate(id, statement, why)(T := of[X], p := expr)`** fixes opaque
types and parameters. It has no obligation.

**`contract(id, statement, why)(post)`** is for a model `(A, B) => R`. `post`
must hold for every call.

**`design(id, statement, why)(files*)`** is a decision with no formal model.
It has nothing to prove, and its files are tracked for change.

**Examples:**

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

`Int` is an unbounded integer in Lean. Do not rely on overflow.

## Proving a link

1. If `check` reports a link `open` with "frflow_auto found no proof", first
   ask whether the obligation is true. Usually it is not, and the node is
   wrong.
2. If it is true, run `scaffold(node)` and prove `theorem link : Obl.link` in
   the proof file. Start with `unfold Obl.link`, then `intro m h`, then
   `simp only [frflow_defs] at *`.
3. The file may contain only the theorem and its tactic proof. Anything else
   is rejected: `sorry`, `axiom`, `run_cmd`, `#eval`, attributes, extra
   imports, and so on. Accepted proofs are also replayed through the Lean
   kernel.
4. `check` also rejects a link that is **vacuous**: one where `abs` alone makes
   the parent hold, whatever the node's spec says, when `frflow_auto` shows it.
   Never write a proof that does not use the node's spec.
5. **Never prove a link from a contradiction in the node** (for example by
   deriving `False` from its spec). The automatic unsatisfiability check does
   not catch every contradiction; the developer reads authored proofs.
