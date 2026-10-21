---
name: frflow
description: Develop a system with FrFlow, where a knowledge base of Scala nodes is proven in Lean from the root idea down to an enforced implementation. Use when stating an idea as a root, adding or changing a node (refine, instantiate, contract), proving a link that automation did not prove, or attaching an implementation to a contract. Also use when the work touches IDEA.md, frflow.json, `Node.root`, `.refine`, `.instantiate`, `.contract` or `.enforce`.
---

# Developing with FrFlow

FrFlow keeps a system connected to its idea, formally. The developer writes the
idea in `IDEA.md`. The knowledge base is a tree of **nodes**, which are Scala vals:

- the **root** states the idea as a predicate over generic types;
- each other node specializes its parent;
- Lean proves every link to the parent, and every node gets a theorem that the
  root holds for it.

The implementation is ordinary Scala attached to a contract node.

**Your job:** build and extend the tree so that every link is proven, and keep
the theory readable for the developer, who approves each node.

## Rules

1. **The Scala definitions are the model.**
   - Never edit `lean/FrFlowGen/` or `lean/FrFlowAudit/`. They are generated
     by `render`.
   - Lean you write goes only in `lean/Proofs/<KB>/<NODE>.lean`.
2. **Do not approve nodes.** Approval is the developer's decision.
   - There is no tool for it. Do not run `approve` from a shell.
   - Do not edit `.frflow/ledger.json`.
3. **Do not weaken the root to make a proof go through.**
   - If a link is false, the child node is wrong: fix the child.
   - If you believe the idea itself is wrong, explain why and ask the developer.
4. **Every statement must say in plain words what its predicate says.** The
   developer reviews both.
5. **The implementation stays plain Scala.** Attach it with `enforce`. Do not
   bend it to fit the DSL.
6. **After any change, `render`.** When a link changed, `check` it. Report
   what is proven, open or failed.

## Tools

The MCP server `frflow` (see `.mcp.json`) works on every project under
`examples/`. Pass `project` when there is more than one.

| tool | use |
|---|---|
| `tree` | Fast. The last snapshot, with link status per node. Says if sources changed since. |
| `context(node)` | **Read before changing a node.** The idea, the path from the root with sources, the obligation, the rules. |
| `render` | Rebuild from the Scala definitions: Lean files and the snapshot the browser shows. Compile errors in the model come back here. |
| `check(node?)` | Prove the links in Lean and record the results. Slow (minutes). |
| `scaffold(node)` | Create the proof file for an obligation `frflow_auto` did not prove. |
| `node(node)` | One node from the snapshot as JSON: obligation, link, root theorem, generated Lean. |
| `status` | The tree with approval and verification, from the current definitions. |
| `history` | The latest events (who rendered, checked, approved what). |

Without MCP, use the CLI of the knowledge base from the repository root:
`sbt "auth/run render"`, `check [NODE]`, `status`, `context NODE` and
`scaffold NODE`.

The developer follows the work in the browser:
`python3 tools/frflow/server.py examples`. The browser updates by itself when
you render or check.

## The workflow

### 1. From the idea to the root

1. Read `IDEA.md`. Find the one property that must always hold. That is the
   root. It is usually a safety property: "never X unless Y".
2. Make every concept the idea does not define generic:
   - `Opaque` for a type;
   - `Param` for a relation or value.

   The root must not assume anything the idea does not say.
3. The model type `M` is what the system does at this level, usually a
   function. The spec is a predicate on `M`.

```scala
val User       = Opaque("User")
val Resource   = Opaque("Resource")
val authorized = Param[(User.T, Resource.T) => Boolean]("authorized")

val noUnauthorizedAccess = Node.root[(User.T, Resource.T) => Boolean](
  "NoUnauthorizedAccess",
  "A user is never granted access to a resource they are not authorized to access."
)(allows => forall((u: User.T, r: Resource.T) => allows(u, r) ==> authorized(u, r)))
```

### 2. Specialize, one decision per node

**`refine`** introduces a more concrete model.
- `abs` maps the new model to the parent's model.
- Obligation: `spec m → parent.spec (abs m)`.
- Introduce new opaques and params for new generic concepts.

```scala
val authenticated = noUnauthorizedAccess.refine[(Token.T, Resource.T) => Option[User.T]]("Authenticated", "...")(
  abs  = decide => (u, r) => exists((t: Token.T) => decide(t, r) == Some(u)),
  spec = decide => forall((t: Token.T, r: Resource.T) => decide(t, r).forall(u => holder(t) == Some(u) && authorized(u, r))))
```

**`instantiate`** fixes opaque types and params with domain types (case
classes, enums) and expressions. It has no obligation: the parent's theorems
apply. New params, such as `grants`, stay open.

```scala
grantBased = authenticated.instantiate[(String, Path) => Option[UserId]]("GrantBased", "...")(
  User := of[UserId], Resource := of[Path], Token := of[String],
  authorized := ((u: UserId, p: Path) => grants.value.contains(Grant(u, p))),
  holder     := ((t: String) => sessions(t)))
```

**`contract`** applies to a node whose model is `(A, B) => R`. `post(a, b, r)`
must hold for every call of the implementation. Obligation: the contract
implies the parent.

**The implementation** is any Scala. Wrap it with `enforce` to check every
result against `post` and bind every param it uses.
`ContractViolation` means the implementation is wrong, not the contract.

```scala
decisionContract.enforce(SessionStore(table.toSet, tokens).decide)(grants.bind(table), sessions.bind(tokens.get))
```

Then add the node to the `KnowledgeBase(...)` list, `render`, and `check`.

**What makes a good node:**
- one design decision;
- a statement a developer can approve without reading Lean;
- generic until a concrete choice is needed.

Prefer a chain of small refinements over one large jump. Small links are
proven automatically far more often.

### 3. The Scala subset in node lambdas

A small macro translates node lambdas to Lean. Anything else is a compile
error that starts with `FrFlow: not supported in a model`. When you get one,
rewrite the expression with what is supported. If it is a domain function,
make it a `define { ... }`.

The macro supports:
- fields, case class constructors, `copy`, `match` and `if`;
- `==` and `!=`;
- `&&`, `||` and `!`;
- integer `+ - * / %`, comparisons, `min` and `max`;
- `==>`, `forall(...)` and `exists(...)` over one or two typed binders;
- on `List`: `contains`, `exists`, `forall`, `filter`, `map`, `length`/`size`,
  `isEmpty`/`nonEmpty` and `++`;
- on `Option`: `forall`, `exists`, `map`, `getOrElse`, `isDefined` and `isEmpty`;
- params, applied (`authorized(u, r)`) or as `.value`;
- `define`d functions.

`Int` and `Long` are unbounded integers in Lean. Do not rely on overflow.

### 4. Proving a link

1. Run `check`. If the link is `open` with "frflow_auto found no proof",
   read `context(node)`.
2. **First ask whether the obligation is true.** A false obligation is the most
   common cause: a missing conjunct in the child's spec, or an `abs` that does
   not preserve what the parent needs. Fix the node. Do not prove around it.
3. If it is true, run `scaffold(node)` and write the proof in
   `lean/Proofs/<KB>/<NODE>.lean`:
   - The file states `theorem link : Obl.link`. Keep that statement exactly.
     A proof of anything else is `failed`.
   - Start with `unfold Obl.link`, then `intro m h` and
     `simp only [frflow_defs] at *`. This unfolds the generated specs.
   - Then use ordinary Lean: `intro`, `cases`, `omega`, `simp`, `grind`, and
     lemmas from core Lean.
   - Rejected: `sorry`, `axiom`, `admit`, `native_decide`, `opaque`,
     `implemented_by`, `extern` and `unsafe`.
   - Allowed axioms: `propext`, `Classical.choice` and `Quot.sound`.
4. Run `check(node)` again. It reports `proven (authored)` when the proof is
   accepted.

### 5. Reporting

When you finish a change, give the developer:
- the nodes you added or changed and their statements;
- each link's state (`proven auto`, `proven authored`, `open`, `failed`);
- what remains open and why.

Remind them that new and changed nodes need their approval. They can approve
in the browser or with `approve NODE --by NAME`.

## Link states

| state | meaning |
|---|---|
| `proven` (auto) | `frflow_auto` proved the obligation |
| `proven` (authored) | your proof in `lean/Proofs` was accepted |
| `proven` (instantiation) | no obligation; the parent's theorems apply |
| `open` | not proven yet: automation failed, or the proof has `sorry` or errors |
| `failed` | the proof states something other than `Obl.link`, uses a forbidden construct, or the theorems or axioms do not pass |
| `stale` | the definitions changed since the last check |
| `not-checked` | never checked |

A node's verification is `proven` only when its link and every link above it
are proven. Its approval is `changed` when its statement, sources or generated
Lean changed after approval.
