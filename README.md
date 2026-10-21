# FrFlow: formal refinement flow for agentic software development

FrFlow applies the refinement discipline of formal hardware design to software
built with AI agents. It develops a program as a layered theory written in Scala.
The theory starts with a domain and requirements and is refined, one proven step
at a time, down to an implementation that runs.

- **The model is Scala.** Domain concepts are Scala ADTs (case classes and enums)
  with pure methods. Requirements, design steps and the implementation are layers
  of a Scala DSL, and every guard, effect, invariant and abstraction is an ordinary
  Scala lambda over those ADTs.
- **Lean is an artifact.** A compile-time macro translates the Scala definitions
  to Lean 4, together with the proof obligations of every layer. No Lean is
  written by hand as part of a model.
- **The implementation is the last refinement.** The bottom layer is executable
  Scala. The same code that runs is the code that is proven to refine the layers
  above it, so the requirements hold for the running system.
- **Proofs are tried automatically first.** Every obligation is attempted with
  `frflow_auto`. Only the obligations automation cannot prove need a proof, which
  an agent writes in a separate Lean file, never in the model.

## Problem

- **Uncontrolled refinement.** Agents add logic incrementally, without an
  explicit relation to the intent, so correctness and design coherence cannot
  be tracked. In FrFlow, every operation of a refining layer, down to the
  executable implementation, must say which parent operation it refines, or that
  it refines `skip`. It is accepted only with proofs that it does so.
- **Lost theory** (Naur, *Programming as Theory Building*, 1985). The program
  is the visible part of a theory held by its programmers. With agents, the
  human often never builds that theory, and the agent loses it when its context
  is compressed. In FrFlow, the theory is explicit and persistent:
  - the domain as Scala ADTs, with laws and assumptions;
  - layers with short statements and rationale;
  - humans approve each node, and an approval is bound to a hash of what was reviewed;
  - agents receive a bounded **slice** of the model for each piece of work.

The underlying division of labor is this:
- **The domain, statements, layers and links** are the theory. They are small,
  reviewed by people, and change rarely.
- **Proofs** are only checked. Any valid proof is acceptable, so automation and
  agents may produce them freely.

Current coverage. The guarantees apply to code inside the model. These are not
covered yet (see Next steps):
- Code outside the model, such as I/O adapters, is not checked.
- Nothing enforces the check on every change.
- Only safety is proven: a layer whose guards never hold still refines its parent.
- An implementation layer's approval also covers its operation bodies, so changing
  the implementation requires a new review.

## The layered model

| Layer | What it contains | Proof obligations |
|---|---|---|
| **Theory** | Domain ADTs and their methods; laws (properties of domain functions); assumptions about the environment | each law |
| **Requirements** (root) | the most abstract state and operations, and the requirements they must satisfy | the requirements are inductive invariants |
| **Design** (0 or more) | a refinement step: new state, new operations, an abstraction to the parent | refinement of the parent, and invariants |
| **Implementation** (leaf) | concrete data and executable operations, with an initial value | refinement of the parent |

Each refining layer gives an abstraction function to its parent's state. Each of
its operations either refines a parent operation, with a witness for the parent's
parameters, or refines `skip`, meaning it leaves the parent state unchanged.
The Lean kernel proves that every requirement and invariant of an ancestor holds,
through the chain of abstractions, in every reachable state of every layer below it,
the implementation included.

```
Scala model (one source)
  domain ADTs, laws, assumptions
  Requirements → Design → … → Implementation
        │
        │  compile-time macro: Scala trees → FrFlow IR
        ▼
  ┌──────────────────────────────┬──────────────────────────────────────┐
  │ executable Scala             │ Lean 4, generated                    │
  │ frflow.runtime.Service runs  │ Domain.lean: structures, inductives, │
  │ the implementation layer     │   functions                          │
  │                              │ <Layer>/Model.lean, Obligations.lean │
  │                              │ <Node>/Auto.lean: frflow_auto        │
  │                              │ <Node>/Assembly.lean: kernel         │
  │                              │   theorems (refinement, transfer)    │
  └──────────────────────────────┴──────────────────────────────────────┘
        │                                   │
        │                        Proofs/<Theory>/<Node>.lean
        │                        (authored, only where automation fails)
        ▼                                   ▼
  check: Lean build, per-obligation status, exact-statement check, axiom audit
  ledger (.frflow/ledger.json): approvals bound to spec hashes, check results
  slices (.frflow/slices/<Node>.md): bounded context for an agent
  digest (THEORY.md): the theory, for people
```

## Example: authorization platform

`examples/authz` is a complete model, from requirement to running service. All 27
obligations are proven by automation.

```
Theory Authz        domain, 3 laws, assumptions A1 and A2
└── R0  NoUnauthorizedAccess (requirements)
    └── D1  AuthnThenAuthz (design)     [assumes A1, A2]
        └── I2  RbacService (implementation, executable)
```

**Theory.** The domain is a set of Scala ADTs, used as they are by the implementation:

```scala
final case class UserId(name: String)
enum Action:
  case Read, Write, Delete
final case class Permission(role: Role, resource: ResourceId, action: Action)

final case class RbacPolicy(roles: Map[UserId, Set[Role]], permissions: Set[Permission]):
  def permits(user: UserId, resource: ResourceId, action: Action): Boolean =
    roles.get(user).exists(held => held.exists(role => permissions.contains(Permission(role, resource, action))))

object AuthzTheory extends Theory("Authz"):
  domain[(UserId, ResourceId, Action, Token, Role, Permission, RbacPolicy, Access)]
  val A1 = assumption("A1", "TokenHolderIsPrincipal", statement = "...", justification = "...")
  law("RevokeAllDenies", "A principal whose roles are all revoked is permitted nothing.") {
    (p: RbacPolicy, u: UserId, r: ResourceId, a: Action) => !p.revokeAll(u).permits(u, r, a)
  }
```

**R0, requirements.** This layer states the security goal without any mechanism:

```scala
object R0 extends Requirements[AuditState](AuthzTheory, "R0", "NoUnauthorizedAccess", statement = "...", rationale = "..."):
  init(s => s.version == 0 && s.log.isEmpty)
  val access = operation[AccessAs]("access")
    .check((s, p) => s.policy(s.version)(p.user, p.resource, p.action))
    .act((s, p) => s.copy(log = Access(p.user, p.resource, p.action, s.version) :: s.log))
  val setPolicy = operation[SetPolicy]("setPolicy").act(...)
  requirement("Safe", "...") { s =>
    s.log.forall(e => e.version <= s.version && s.policy(e.version)(e.user, e.resource, e.action))
  }
```

**D1, design.** Sessions bind tokens to principals; `login` and `logout` are new
operations that refine `skip`. D1 relies on assumptions A1 and A2 for the link
between a token and the real requester.

**I2, implementation.** Policies are RBAC data, kept by version. Every operation
is executable, and the witness of `publish` maps RBAC data to the abstract policy:

```scala
object I2 extends Implementation[ServiceState, SessionState](D1, "I2", "RbacService", statement = "...", rationale = "..."):
  abstraction(s => SessionState(s.version, v => (u, r, a) => s.permittedAt(v, u, r, a), s.sessions, s.log))
  initial(ServiceState(0, Map.empty, Map.empty, Nil))
  val access = operation[Request]("access")
    .check((s, r) => s.allows(r))
    .act((s, r) => s.copy(log = Access(s.principal(r.token), r.resource, r.action, s.version) :: s.log))
    .refines(D1.access)((_, r) => r)
  val publish = operation[PublishPolicy]("publish")
    .act((s, p) => s.copy(version = s.version + 1, policies = s.policies.updated(s.version + 1, p.policy)))
    .refines(D1.setPolicy)((_, p) => SetPolicy((u, r, a) => p.policy.permits(u, r, a)))
```

`AuthzService` runs I2 with `frflow.runtime.Service`. The check proves
`Authz.I2.inherits_R0_Safe`: the audit log of the running service satisfies the
requirement in every reachable state. The proof depends only on Lean's standard
axioms (`propext`, `Classical.choice`, `Quot.sound`), under assumptions A1 and A2.

The integration tests (`AuthzIntegrationSuite`) cover these failure modes:
- An `adminAccess` operation that skips the policy decision is rejected: its guard
  obligation cannot be proven.
- A proof of a weaker statement does not count.
- A law that automation cannot prove (nonlinear arithmetic) is closed by an authored
  proof in `Proofs/`, kept apart from the model.
- Rewording one layer's statement invalidates only that layer's approval.

## Proofs

1. `render` generates, for every node, an `Auto.lean` that tries
   `frflow_auto` on each obligation. The tactic is in the kernel: it unfolds all
   generated definitions (`@[frflow_defs]`), simplifies, and closes the remaining
   goals with `grind`, function extensionality and case splits.
2. `check` attributes Lean's errors to individual obligations. An obligation that
   automation does not prove is reported as `open`.
3. `scaffold <Node>` adds stubs for open obligations to
   `Proofs/<Theory>/<Node>.lean`. An agent writes `theorem <name> : Obl.<name>`
   there. An obligation with an authored proof is no longer attempted automatically.
4. The checker requires each authored theorem to state exactly `Obl.<name>`. It
   rejects `axiom`, `admit`, `native_decide`, `implemented_by`, `extern`,
   `unsafe` and `opaque`, builds the assembly, and audits the axioms of every
   resulting theorem.

The theory is not changed by writing proofs. If an obligation is false, the
model must change, in Scala, and the change must be approved again.

## The Scala subset

The macro translates:
- **Types:**
  - case classes and Scala 3 enums, including enum cases with fields;
  - `Boolean`, `Int`, `Long`, `BigInt` and `String`;
  - immutable `List`, `Set`, `Map` and `Option`;
  - tuples and function types.
- **Expressions:**
  - lambdas, `val`, `if`, and `match` on constructors and literals;
  - constructors, `copy` and field access;
  - methods of ADTs, and functions and values in objects (read from their definitions);
  - the usual operations on the collections above.
- **Specification only:** `forall`, `exists` and `==>` from `frflow.dsl`. These
  are rejected in implementation layers.

Anything else is a compile error at its source position, for example a `var`,
I/O, a partial operation such as `Map.apply` or `List.head`, a sealed trait
hierarchy, or a reference to a local value outside the expression. A project that
uses the DSL compiles with `-Yretain-trees` (the macro reads method bodies) and
`-Xread-docs` (Scaladoc is carried into the Lean and the digest).

Semantics of the translation:
- `Boolean` becomes `Prop`.
- `Map[K, V]` becomes `K → Option V` and `Set[A]` becomes `A → Prop`. Both are
  compared extensionally, as Scala compares immutable collections.
- Case classes become structures, and enums become inductive types.

## What is trusted

- **The Lean kernel and FrFlow's Lean kernel** (`lean/FrFlow/`): the transition
  systems, refinement and its safety transfer, event machines, the Scala prelude
  (`FrFlow/Scala.lean`), and the `frflow_auto` tactic. The tactic only produces
  proof terms, which Lean checks.
- **The translation** (`frflow.lift`, `frflow.render.LeanPrinter`): it must give
  each supported Scala construct its Scala meaning. Known gap: Scala's `Int` and
  `Long` wrap on overflow, while Lean's `Int` is unbounded. Proofs therefore assume
  that no arithmetic overflows.
- **The runtime** (`frflow.runtime.Service`): it applies an operation only when its
  `check` clauses hold, and serializes calls. `assume` clauses are environment
  assumptions and are not evaluated.
- **The assumptions** cited by the layers.

## Usage

Requirements: JDK 17+, sbt, and Lean 4.35.0 (`lake` on the PATH, or `FRFLOW_LAKE`).

```sh
sbt test                        # unit tests; Lean integration tests run when lake is available
sbt "authz/run lint"
sbt "authz/run render"          # generate Lean from the Scala model
sbt "authz/run check"           # verify; results go to the ledger
sbt "authz/run status"
sbt "authz/run scaffold I2"     # proof stubs for obligations automation did not prove
sbt "authz/run approve D1 --by <name>"
sbt "authz/run slice D1"        # bounded context for an agent working on D1
sbt "authz/run digest"          # regenerate THEORY.md
sbt "authz/run demo"            # run the implementation
```

Nodes are `Theory` and the layer ids.

## Repository layout

```
lean/FrFlow/             Lean kernel: Spec, Refinement, Machine, Scala prelude, frflow_auto
modules/core/            frflow-core
  ir/                    typed IR of the translated Scala subset, JSON codec
  lift/                  compile-time macro: Scala trees → IR (Code, Schema)
  dsl/                   Theory, Requirements, Refinement, Implementation, Operation, Model
  model/                 immutable snapshot of a model
  runtime/               Service: runs an implementation layer
  render/                IR → Lean, generated modules
  obligation/ check/ lint/ ledger/ report/ cli/
examples/authz/          domain, theory, layers R0/D1/I2, service, tests,
                         generated Lean, ledger, slices, THEORY.md
```

## Next steps

1. Enforcement: a CI gate that builds Lean, runs `check`, and fails when a node
   is not proven or not approved.
2. Code outside the model: run operations only through `Service` (make
   `Operation.apply` internal), and detect logic that no layer justifies.
3. Enabledness and liveness: require a refining operation to be enabled whenever
   its parent operation is, and variants for new operations, so that refinement
   cannot only stutter.
4. Approval scope: bind an implementation layer's approval to its statement,
   state, abstraction and assumptions rather than its operation bodies, which the
   refinement proofs already constrain.
5. Bounded integers: model `Int` and `Long` with wrap-around, or generate
   no-overflow obligations.
6. Laws as lemmas for automation: let `frflow_auto` use proven laws.
7. Sealed trait hierarchies and recursive functions, with termination.
8. Agent interface: an MCP server with role-restricted operations (propose a
   layer, submit a proof, request a model change), gated by the checker and by
   approvals.
9. Decomposition: several implementation leaves (components) refining one design.
