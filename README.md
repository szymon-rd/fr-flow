# FrFlow

FrFlow keeps the theory of a software project — what it must do and why it is
built this way — explicit, decided by a person, and connected to the code. It
also shows when anything drifts from it.

## Problem

- **Uncontrolled refinement.** Agents add logic incrementally, without an
  explicit relation to the intent, so correctness and design coherence cannot
  be tracked.
- **Lost theory** (Naur, *Programming as Theory Building*, 1985). The program
  is the visible part of a theory held by its programmers: why it is the way it
  is, how it maps to the world, what would have to change if the world did.
  With agents, the human often never builds that theory, and the agent loses
  it when its context is compressed.

## The method

The developer writes the idea in `IDEA.md`. The project's knowledge is a
**tree**:

- each **root** states one concern of the idea;
- each node below **specializes its parent**, one design decision at a time;
- at the bottom, a **contract** is what the implementation must satisfy on
  every call.

| A node has | It answers | Kept by |
|---|---|---|
| a statement | what holds at this level, in plain words | the Scala source |
| `why` | why this step: the reason, and what it assumes about the world | the Scala source |
| a formal model | the same, precisely (Scala, translated to Lean) | the Scala source |
| examples (contracts) | what it means in concrete cases | the Scala source |
| a decision | who chose it, why, and which alternatives were rejected | `.frflow/ledger.json` |

**The theory is built by deciding.**
1. The developer asks for a next step in the browser.
2. The agent proposes one or more alternative nodes, each with its reason and
   examples.
3. The developer compares them and chooses one, with a reason of their own.
4. The decision keeps that reason and the rejected alternatives.

The developer does not just approve what the agent wrote: they make every
choice. An agent picking up the work later reads the same record through
`context`.

**Drift is caught in three ways.**

- **The design drifts from its decisions.** A decision is bound to a hash of
  the node as decided, chained to its ancestors.
  - If the node changes, it shows as `changed`, with a diff against what was
    decided.
  - If anything above it changes, it shows as `parent-changed`, and the
    developer confirms it still holds.
  - Nothing changes silently.
- **The levels drift from each other.** Lean proves that each node implies its
  parent, so every node, down to the contract, satisfies the root.
- **The behaviour drifts from what was decided.** The contract's examples run
  against the contract and against the implementation.
  - An implementation that stops doing what was decided fails its examples.
  - So does a contract that refuses everything, even though it is trivially
    "safe".
  - In production, `enforce` checks every result against the contract.

**The tree states its own limits.** What the idea says but the tree does not
model is listed under `## Not modelled` in `IDEA.md`.

## Example: access control (`examples/auth`)

```scala
val User       = Opaque("User")       // a type the idea leaves open
val Resource   = Opaque("Resource")
val authorized = Param[(User.T, Resource.T) => Boolean]("authorized")   // a value it leaves open

val noUnauthorizedAccess = Node.root[(User.T, Resource.T) => Boolean](
  "NoUnauthorizedAccess",
  "A user is never granted access to a resource they are not authorized to access.",
  why = "This is the one thing the idea says must never happen."
)(allows => forall((u: User.T, r: Resource.T) => allows(u, r) ==> authorized(u, r)))

val authenticated = noUnauthorizedAccess.refine[(Token.T, Resource.T) => Option[User.T]](
  "Authenticated",
  "A request is granted on behalf of a user only if its token belongs to that user and the user is authorized.",
  why = "Users identify themselves with tokens they receive at login, so a decision sees a token, not a user."
)(
  abs  = decide => (u, r) => exists((t: Token.T) => decide(t, r) == Some(u)),
  spec = decide => forall((t: Token.T, r: Resource.T) => decide(t, r).forall(u => holder(t) == Some(u) && authorized(u, r))))

val grantBased = authenticated.instantiate[(String, Path) => Option[UserId]]("GrantBased", "...", why = "...")(
  User := of[UserId], Resource := of[Path], Token := of[String],
  authorized := ((u: UserId, p: Path) => grants.value.contains(Grant(u, p))),
  holder     := ((t: String) => sessions(t)))

val decisionContract = grantBased.contract[String, Path, Option[UserId]]("DecisionContract", "...", why = "...")(
  (token, path, decision) => decision.forall(u => sessions(token) == Some(u) && grants.value.contains(Grant(u, path))))
  .examples(grants.bind(List(Grant(alice, Path("/a")))), sessions.bind(Map("t1" -> alice).get))(
    expect("t1", Path("/a"), Some(alice), "Alice's token and a grant for /a: she gets in"),
    reject("t1", Path("/b"), Some(alice), "access without a grant is never given"))

val knowledge = KnowledgeBase("Auth", idea = "IDEA.md")(noUnauthorizedAccess, authenticated, grantBased, decisionContract)
  .implement(decisionContract)(SessionStore(grants.value.toSet, sessions.value).decide)

// In production: plain Scala, every result checked against the contract.
def service(grantTable: List[Grant], tokens: Map[String, UserId]) =
  decisionContract.enforce(SessionStore(grantTable.toSet, tokens.get).decide)(grants.bind(grantTable), sessions.bind(tokens.get))
```

When this tree was built, the agent proposed two ways to go below the root:
- `Authenticated`: requests carry tokens;
- `ClientAsserted`: the client names its user.

The developer chose `Authenticated`: *"The idea says users identify
themselves with tokens; a client's own claim is not proof."* The rejected
option and that reason live in the ledger and show in the browser and in
`context`.

`examples/crm` does the same for a multi-tenant CRM.

## The node kinds

| Kind | Written as | Proof |
|---|---|---|
| root | `Node.root[M](id, statement, why)(spec)` | none: it is the statement |
| refine | `parent.refine[M2](id, statement, why)(abs, spec)` | Lean: `spec m → parent.spec (abs m)` |
| instantiate | `parent.instantiate[M2](id, statement, why)(T := of[X], p := ...)` | none: the generic results apply |
| contract | `parent.contract[A, B, R](id, statement, why)(post)` | Lean: the contract implies the parent |

- `Opaque("User")` is a type with no assumed structure. In Lean, it is a type
  parameter.
- `Param[A]("authorized")` is a value left open. In Lean, it is a parameter:
  everything proven holds for every value of it.
- `define { ... }` is a named function of the domain.
- The domain is Scala case classes and enums.

A small macro translates node lambdas to Lean. Anything it does not support is
a compile error. Links are proven by the tactic `frflow_auto`, or, failing
that, by a proof the agent writes in `lean/Proofs/<KB>/<NODE>.lean`. That
proof must state exactly `Obl.link` and may contain only tactics.

## The browser: where decisions are made

```sh
python3 tools/frflow/server.py examples     # http://127.0.0.1:8765
```

- **Tree.** The tree is drawn from the Scala definitions. Each link to a parent
  is green when proven. Proposals have a dashed outline.
- **Node.** For each node:
  - its statement and `why`;
  - **the decision**: choose between proposals with your reason, accept a
    change after seeing its diff, or confirm a node whose parent changed;
  - its examples, with results against the contract and the implementation;
  - the link to the parent, side by side with the parent;
  - the root theorem;
  - a box to **ask the agent** for something.
- **Inbox.** What waits for your decision, and the agent's answers to your
  requests.
- **Idea.** `IDEA.md`, editable. Saving re-renders, and the roots then need
  confirming.
- **Domain, History.** The types and parameters of the model, and every
  render, check and decision, with who made it.

## Agents

- **MCP server.** `.mcp.json` registers `frflow` (`tools/frflow/mcp_server.py`).
  - Tools: `inbox`, `context`, `render`, `check`, `answer`, `scaffold`, `tree`,
    `node`, `status` and `history`.
  - An agent cannot accept nodes.
- **Skill.** `.claude/skills/frflow/SKILL.md` gives the agent its loop:
  1. Read the inbox.
  2. Propose alternatives with reasons and examples.
  3. Render and check.
  4. Answer the request.
  5. Remove the rejected nodes once the developer has decided.

## What is proven, checked, and trusted

- **Proven by Lean:** every link, and so every node's root theorem.
- **Checked by the examples:** that the contract means what its statement says,
  and that the implementation does what was decided, in those cases.
- **Enforced at run time:** every result meets the contract, or
  `ContractViolation` is raised.
- **Decided by the developer:** every node, with its reasons. The decision is
  only as good as their reading. Examples and the side-by-side link are there
  to make that reading possible.
- **Trusted:**
  - the Scala-to-Lean translation;
  - `Int` read as unbounded;
  - run-time parameter values are the data the theorems talk about;
  - every path to the data goes through the enforced implementation.
- **Not covered:** properties over time or state, such as revocation or
  expiry. Contracts are per call.

## Usage

Requirements: JDK 17+, sbt, Lean 4.35.0 (`lake` on the PATH, or `FRFLOW_LAKE`),
and Python 3.10+ for the browser and the MCP server.

```sh
sbt test                                  # unit tests, and Lean tests when lake is available
sbt "auth/run render"                     # Lean and the snapshot .frflow/kb.json, from the Scala definitions
sbt "auth/run check"                      # render, prove the links, record the results
sbt "auth/run status"                     # decisions, proofs and examples
sbt "auth/run context Authenticated"      # everything known about a node, for agents and people
sbt "auth/run accept Authenticated --by <name> --note <reason> [--reject ClientAsserted]"
python3 -m unittest discover -s tools/frflow/tests
```

## Layout

```
lean/FrFlow/          the Lean side of the library: the frflow_auto tactic
core/                 the Scala library
  Model.scala         Opaque, Param, define
  Lift.scala          the macro: Scala lambdas to Lean
  Node.scala          nodes, examples, the knowledge base, enforce
  Generate.scala      Lean generation
  Workflow.scala      check, decisions, status, context, snapshot, event log
examples/auth/        access control: idea, model, implementation, ledger
examples/crm/         multi-tenant CRM, the same
tools/frflow/         browser (server.py, ui/index.html) and MCP server (mcp_server.py)
.claude/skills/frflow the agent skill
```
