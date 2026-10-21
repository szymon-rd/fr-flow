# FrFlow: formal refinement flow for agentic software development

FrFlow applies the refinement discipline of formal hardware design to software
built with AI agents. A program is developed as a **theory tree**:

- the root states what must hold;
- each child refines its parent toward an implementation;
- every link is proven in Lean 4.

Agents work inside this structure. A change is accepted only when all
refinement obligations still hold, and the theory itself lives in the tree
rather than in agent context or a set of loose documents.

## Motivation

- **Uncontrolled refinement.** Agents add logic incrementally, without an
  explicit relation to the intent, so correctness and design coherence cannot
  be tracked. In FrFlow, every event of a refining node must say which parent
  event it refines, or that it refines `skip`. It is then accepted only with
  proofs that it does so.
- **Lost theory** (Naur, *Programming as Theory Building*, 1985). The program
  is the visible part of a theory held by its programmers. With agents, the
  human often never builds that theory, and the agent loses it when its context
  is compressed. In FrFlow, the theory is explicit and persistent:
  - short statements, rationale and formal models, organized as a tree;
  - humans approve statements;
  - agents receive a bounded **slice** of the tree for each piece of work.

The underlying division of labor is this:
- **Statements, models and links** are the theory. They are small, reviewed by
  people, and change rarely.
- **Proofs** are only checked. Any valid proof is acceptable, so agents may
  produce them freely.

## How it works

```
Scala DSL (theory)
  │  lint: structure and coherence rules
  ▼
Lean sources, generated            Proofs, authored
  Model.lean        ← approved      Proofs/<Theory>/<Node>.lean
  Obligations.lean  ← derived         theorem <name> : Obl.<name>
  Assembly.lean     ← consumes proofs, builds kernel theorems
  │  check: lake build, per-obligation attribution, axiom audit
  ▼
Ledger (.frflow/ledger.json): approvals bound to spec hashes, check results
Slices (.frflow/slices/<Node>.md): bounded context for agents
Digest (THEORY.md): the theory, for people
```

### Nodes

Each node is an event machine in the style of Event-B. It has:
- state fields, an initial condition, and guarded events;
- invariants;
- a link to its parent: an abstraction function `abs` and an optional gluing
  invariant `glue`.

Each event has two kinds of guard clause:
- **`check` clauses:** what the implementation must enforce.
- **`assume` clauses:** environment assumptions. Each one cites a declared
  assumption, so trust is explicit and never hidden in a model.

### Obligations

Obligations are generated per node and per event:

| Obligation | Meaning |
|---|---|
| `init_<I>` | initial states satisfy invariant `I` (including `glue`) |
| `<e>_inv_<I>` | event `e` preserves invariant `I` |
| `init_abs` | initial states map to parent initial states |
| `<e>_grd` | guard strengthening: `e` enabled ⇒ the parent event is enabled for the witness |
| `<e>_sim` | simulation: `abs` of the new state = the parent event's effect |
| `<e>_skip` | a new event does not change the parent state |

### Kernel

The Lean kernel (`lean/FrFlow/`) is small, hand-written, and is the trusted base.
- `Machine.refinement` and `Machine.invariant` assemble per-event obligations
  into a `Refinement` and machine invariants.
- `Refinement.transfer` carries every invariant of an ancestor down to the
  refined node.

In the example, the root property `Safe` is therefore proven for T1 as
`Authz.T1.inherits_T0_Safe`, under assumption A1 and depending only on Lean's
standard axioms.

### What the checker enforces

- Generated models and obligations type-check. A failure here is a model error.
- Every obligation has a theorem whose statement is **exactly** `Obl.<name>`.
  An agent cannot prove a weaker statement instead.
- `axiom`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe` and
  `opaque` are rejected in proof files.
- `sorry` leaves an obligation open.
- The assembly builds. Proofs therefore compose into the kernel theorems.
- `#print axioms` for each resulting theorem reports only `propext`,
  `Classical.choice` and `Quot.sound`.
- Approval is bound to a hash of the node's statement, rationale, model and
  assumptions. Any change returns the node to `changed` until it is reviewed
  again.

## Example: authorization platform

`examples/authz` contains this tree:

```
T0  NoUnauthorizedAccess
└── T1  AuthnThenAuthz   [assumes A1]
```

- **T0:** "Every recorded access was permitted by the policy in force when it
  was decided." It has a versioned policy history and the invariant `Safe`.
- **T1:** access is mediated by sessions. The implementation checks that the
  token is bound to principal `u` and that the current policy permits `u`.
  - The link between the token and the real requester cannot be observed by
    the system, so it is stated as assumption **A1**.
  - `login` and `logout` are new events that refine `skip`.

The integration tests show the main failure mode the framework exists to
catch. An `adminAccess` event that skips the policy decision cannot be proven
to refine `access`: its guard obligation fails, and the node is rejected.

## Usage

Requirements: JDK 17+, sbt, and Lean 4 through elan. The toolchain is pinned in
`lean/lean-toolchain`.

```sh
sbt test                         # unit tests; integration tests run when `lake` is on PATH
sbt "authz/run lint"
sbt "authz/run render"           # generate Lean sources
sbt "authz/run scaffold"         # create proof stubs for missing obligations
sbt "authz/run check"            # verify with Lean, record results in the ledger
sbt "authz/run status"
sbt "authz/run approve T1 --by <name>"
sbt "authz/run slice T1"         # bounded context for an agent working on T1
sbt "authz/run digest"           # regenerate THEORY.md
```

Without sbt (for example, without access to Maven), use a Scala 3 distribution:
`SCALA_HOME=... scripts/build-offline.sh`, then `scripts/frflow-offline.sh <command>`.

## Writing a theory

```scala
object AuthzTheory extends TheoryDef("Authz"):
  vocabulary(opaqueType("User", "A principal."), typeAlias("Token", "Nat", "Bearer credential id."))

  val A1 = assumption("A1", "PresenterIsSessionPrincipal",
    statement = "A request presenting a token bound to principal u is issued by u.",
    justification = "Tokens are unforgeable and not shared.")

  val T0 = root("T0", "NoUnauthorizedAccess", statement = "...", rationale = "...")(
    NodeSpec(state = ..., init = lean("..."), events = Seq(event("access").params(...).check("...").act("...")),
             invariants = Seq(invariant("Safe", "...")))
  )

  val T1 = T0.refine("T1", "AuthnThenAuthz", statement = "...", rationale = "...")(
    link = link(abs = "{ version := s.version, policy := s.policy, log := s.log }"),
    spec = NodeSpec(events = Seq(
      event("access").params(...)
        .assume(A1, "∀ v, s.sessions p.t = some v → v = p.actor")
        .check("s.sessions p.t = some p.u")
        .check("s.policy s.version p.u p.r p.a")
        .act("...")
        .refines("access", witness = "{ u := p.actor, r := p.r, a := p.a }"),
      event("login").params(...).check("...").act("...").refinesSkip
    ))
  )
```

Inside Lean fragments:
- `s` is the node state, and `p` is the event's parameters.
- Ancestor definitions are referenced by node id, for example `T0.Entry`.

## Repository layout

```
lean/                    Lean kernel package (trusted base)
modules/core/            frflow-core: model, DSL, obligations, renderer, lints,
                         checker, ledger, reports, CLI
examples/authz/          authorization theory, Lean workspace, authored proofs,
                         ledger, slices, THEORY.md
scripts/                 offline build and run scripts
```

## Status and roadmap

This is the MVP of the architecture: the kernel, the theory IR and DSL,
obligation generation, rendering, lints, the checker, the ledger, slices and
the digest. Model expressions are Lean fragments checked by Lean; they are not
parsed by FrFlow.

Planned:
1. **Traceability:** a Scala compiler plugin for `@implements` and
   `@refines`, with detection of code that no node justifies.
2. **Agent interface:** an MCP server with role-restricted operations
   (propose refinement, submit proof, implement leaf, request spec change),
   gated by the checker and by approvals.
3. **Conformance:** executable leaf models, and differential testing of
   effectful Scala code against them.
4. **Verified core:** translation of a pure Scala subset (from TASTy) to Lean,
   or a Stainless bridge.
5. **Extensions:** liveness obligations (variants for new events), component
   decomposition, assumption discharge by child nodes, and a typed expression
   IR for semantic diffs.
