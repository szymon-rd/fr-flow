# FrFlow

FrFlow keeps a software project connected to its idea, formally.

1. The developer writes the idea in `IDEA.md`.
2. An agent states it as the **root** of a knowledge base: a Scala predicate over
   generic types, which becomes a Lean theorem.
3. The root is **specialized** step by step: more concrete models, concrete types,
   and finally a **contract** for the implementation. Lean proves every step,
   and every node gets a theorem stating that the root holds for it.
4. The implementation is ordinary Scala, attached to the contract. Every result
   is checked against the contract, so the root holds for what the running
   system returns.

## Problem

- **Uncontrolled refinement.** Agents add logic incrementally, without an
  explicit relation to the intent, so correctness and design coherence cannot
  be tracked. In FrFlow, every step from the idea to the implementation is a
  node with a proven link to its parent.
- **Lost theory** (Naur, *Programming as Theory Building*, 1985). The program
  is the visible part of a theory held by its programmers. With agents, the
  human often never builds that theory, and the agent loses it when its context
  is compressed. In FrFlow, the theory is explicit and persistent: the idea, a
  tree of nodes with statements and formal models, and human approvals. Agents
  work from a node's context.

## The core idea

A node specifies a **model**: a Scala value, usually a function, describing what
the system does at that level. The node's **spec** says which models are acceptable.

| Step | Written as | Meaning | Proof |
|---|---|---|---|
| root | `Node.root[M](id, statement)(spec)` | the idea | none: it is the statement |
| refine | `parent.refine[M2](id, statement)(abs, spec)` | a more concrete model; `abs` maps it to the parent's model | Lean: `spec m → parent.spec (abs m)` |
| instantiate | `parent.instantiate[M2](id, statement)(T := of[X], p := ...)` | fixes opaque types and parameters | none: the generic results are applied |
| contract | `parent.contract[A, B, R](id, statement)(post)` | what every call `(a, b) => r` of an implementation satisfies | Lean: the contract implies the parent |

Generic parts are values:

- `Opaque("User")`: a type with no assumed structure, used as `User.T`. In Lean,
  a type parameter.
- `Param[A]("authorized")`: a value left open. In Lean, a parameter: everything
  proven holds for every value of it. `.assuming(p)` adds a hypothesis.
- `define { ... }`: a named function of the domain, translated once to Lean.

The domain is Scala case classes and enums. A small macro translates the
lambdas of nodes to Lean: fields, constructors, `copy`, `match`, `if`, Boolean
and integer operators, some `List` and `Option` operations, `forall` and
`exists`. Anything else is a compile error.

## Example: access control (`examples/auth`)

```scala
val User       = Opaque("User")
val Resource   = Opaque("Resource")
val authorized = Param[(User.T, Resource.T) => Boolean]("authorized")

val noUnauthorizedAccess = Node.root[(User.T, Resource.T) => Boolean](
  "NoUnauthorizedAccess",
  "A user is never granted access to a resource they are not authorized to access."
)(allows => forall((u: User.T, r: Resource.T) => allows(u, r) ==> authorized(u, r)))

val Token  = Opaque("Token")
val holder = Param[Token.T => Option[User.T]]("holder")

val authenticated = noUnauthorizedAccess.refine[(Token.T, Resource.T) => Option[User.T]](
  "Authenticated", "A request is granted on behalf of a user only if its token belongs to that user and the user is authorized."
)(
  abs  = decide => (u, r) => exists((t: Token.T) => decide(t, r) == Some(u)),
  spec = decide => forall((t: Token.T, r: Resource.T) => decide(t, r).forall(u => holder(t) == Some(u) && authorized(u, r)))
)

val grantBased = authenticated.instantiate[(String, Path) => Option[UserId]]("GrantBased", "...")(
  User := of[UserId], Resource := of[Path], Token := of[String],
  authorized := ((u: UserId, p: Path) => grants.value.contains(Grant(u, p))),
  holder     := ((t: String) => sessions(t))
)

val decisionContract = grantBased.contract[String, Path, Option[UserId]]("DecisionContract", "...")(
  (token, path, decision) => decision.forall(u => sessions(token) == Some(u) && grants.value.contains(Grant(u, path))))

// The implementation is plain Scala; every result is checked against the contract.
final class SessionStore(grantTable: Set[Grant], tokens: Map[String, UserId]):
  def decide(token: String, path: Path): Option[UserId] = tokens.get(token).filter(u => grantTable.contains(Grant(u, path)))

def service(grantTable: List[Grant], tokens: Map[String, UserId]) =
  decisionContract.enforce(SessionStore(grantTable.toSet, tokens).decide)(grants.bind(grantTable), sessions.bind(tokens.get))
```

Lean proves `Authenticated` once, for all users, resources, tokens and meanings
of "authorized". For the contract it proves, for every grant table and session
table: if every decision meets the contract, no user is granted access a grant
does not allow.

`examples/crm` has the same shape for a multi-tenant CRM. Its root is tenant
isolation: a user sees a record only if it belongs to their company or was
shared with it.

## Proofs

Every link obligation is first attempted by the tactic `frflow_auto`. In both
examples, automation proves all of them. If automation fails, `scaffold NODE`
creates `lean/Proofs/<KB>/<NODE>.lean`, where the proof is written. A proof
must state exactly `Obl.link`. The checker rejects `axiom`, `sorry` and similar
constructs, and audits the axioms of every node's `root` theorem.

## What is proven and what is trusted

- **Proven by Lean:** every link, and therefore every node's `root` theorem.
- **Enforced at run time:** that the implementation's results meet the contract.
  A result that breaks it raises `ContractViolation`, so the system fails closed.
- **Trusted:**
  - the Scala-to-Lean translation (`Lift.scala`) and the generator;
  - `Int` and `Long` are read as unbounded integers in Lean;
  - parameter values bound at run time are the ones the theorems talk about;
  - every path to the data goes through the enforced implementation.

## Usage

Requirements: JDK 17+, sbt, and Lean 4.35.0 (`lake` on the PATH, or `FRFLOW_LAKE`).

```sh
sbt test                               # unit tests, and Lean tests when lake is available
sbt "auth/run check"                   # generate Lean, prove the links, record the results
sbt "auth/run status"                  # the tree, with approval and verification state
sbt "auth/run context Authenticated"   # the idea, the path from the root, the obligation
sbt "auth/run approve Authenticated --by <name>"
sbt "auth/run scaffold Authenticated"  # a proof file, if automation leaves the link open
```

Approvals are bound to a hash of what was reviewed: the statement, the Scala
sources, the generated Lean, and, for the root, the idea. A change shows the
node as `changed` until it is approved again.

## Layout

```
lean/FrFlow/          the Lean side of the library: the frflow_auto tactic
core/                 the Scala library
  Model.scala         Opaque, Param, Lifted, define
  Lift.scala          the macro: Scala lambdas to Lean
  Node.scala          nodes, the knowledge base, enforce
  Generate.scala      Lean generation
  Workflow.scala      check, approve, status, context
examples/auth/        access control: idea, model, implementation, generated Lean, ledger
examples/crm/         multi-tenant CRM, the same
```
