# FrFlow

FrFlow keeps the theory of a software project explicit, decided by a person,
and connected to the code, and it shows when anything drifts from it. The
theory is what the system must do and why it is built this way.

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
**tree** of nodes, written in Scala:

- each **root** states one concern of the idea;
- each node below **specializes its parent**, one design decision at a time;
- **contracts** are what an implementation must satisfy on every call;
- **design** nodes record decisions that have no formal model, such as
  architecture or conventions.

| What is recorded | Where | Why it matters |
|---|---|---|
| the idea, and what it leaves out (`## Not modelled`) | `IDEA.md` | the limits of the theory are explicit |
| the vocabulary: what each open term means in the world | `Opaque("User", "a person who uses the system")`, `Param(..., means)` | how the model maps to the world |
| per node: statement, `why`, formal model | the Scala source | what holds at each level, and the reasoning behind it |
| per contract: examples (`expect` / `reject`) | the Scala source | what it means in concrete cases |
| per node: who chose it, their reason, the alternatives rejected | `.frflow/ledger.json`, append-only | the decisions behind the design |

**The theory is built by deciding.** The developer works in the browser.
1. They ask for a next step.
2. The agent proposes one or more nodes, each with its reason and examples.
3. The developer compares them and chooses one, with a reason of their own.
4. The decision keeps that reason and the rejected alternatives, permanently.

The tree is decided from the root down. An agent picking up the work later
reads the whole record through `context`.

**Drift is caught in four ways.**

| Drift | How it shows |
|---|---|
| A node changes after it was decided | `changed`, with a diff against what was decided. A decision is bound to a hash of exactly what the developer saw: statement, `why`, sources, examples (by value), the definitions and types it uses, the files it governs, and, for a root, the idea. |
| Something above it changes | `parent-changed`. The developer confirms that it still holds, for one node or for a whole subtree at once. |
| The code a node governs changes | "code changed", until the developer confirms. The code is a contract's implementation, or a design node's files. |
| A level stops implying its parent | Lean proves every link. A link that holds whatever the node says is reported as **vacuous**, so a meaningless abstraction cannot turn the tree green. |
| The behaviour stops matching what was decided | Contract examples run against the contract and against the implementation. In production, `service` checks every result against the contract. |

A decided node that disappears from the model is listed as removed until the
developer confirms the removal.

## Example: access control (`examples/auth`)

```scala
val User       = Opaque("User", "a person who uses the system")
val Resource   = Opaque("Resource", "something a user may want to access")
val authorized = Param[(User.T, Resource.T) => Boolean]("authorized",
  "whether the user is allowed the resource, by whatever rule the system adopts")

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

val inMemorySessions = decisionContract.design("InMemorySessions",
  "Sessions and grants are held in memory, in one process.", why = "One service decides access; the tables fit in memory."
)("src/main/scala/auth/SessionStore.scala")

val knowledge = KnowledgeBase("Auth", idea = "IDEA.md")(noUnauthorizedAccess, authenticated, grantBased, decisionContract, inMemorySessions)
  .implement(decisionContract)(SessionStore(grants.value.toSet, sessions.value).decide)

// Production: the registered implementation, with every result checked against the contract.
def service(grantTable: List[Grant], tokens: Map[String, UserId]) =
  knowledge.service(decisionContract)(grants.bind(grantTable), sessions.bind(t => tokens.get(t)))
```

When this tree was built, the agent proposed two nodes below the root:
- `Authenticated`: requests carry tokens;
- `ClientAsserted`: the client names its user.

The developer chose `Authenticated`: *"The idea says users identify
themselves with tokens; a client's own claim about who it is proves nothing.
Revisit if requests come only from trusted services."* The ledger keeps that
reason and the rejected option.

`examples/crm` does the same for a multi-tenant CRM.

## The node kinds

| Kind | Written as | Proof |
|---|---|---|
| root | `Node.root[M](id, statement, why)(spec)` | none: it is the statement |
| refine | `parent.refine[M2](id, statement, why)(abs, spec)` | Lean: `spec m → parent.spec (abs m)`, and not vacuous |
| instantiate | `parent.instantiate[M2](id, statement, why)(T := of[X], p := ...)` | none: the generic results apply |
| contract | `parent.contract[A, B, R](id, statement, why)(post).examples(...)(...)` | Lean: the contract implies the parent |
| design | `parent.design(id, statement, why)(files*)` or `Node.design(...)` | none: decided and tracked |

The building blocks:
- **The domain** is Scala case classes and enums. They must keep structural
  equality.
- **The macro** translates node lambdas to Lean. Anything it does not support
  is a compile error.
- **Proofs.** Links are proven by `frflow_auto`. Failing that, the agent writes
  a proof in `lean/Proofs/<KB>/<NODE>.lean`:
  - it states exactly `Obl.link`;
  - it contains only a tactic proof;
  - it is replayed through the Lean kernel.

## The browser: where decisions are made

```sh
bin/frflow serve examples     # http://127.0.0.1:8765
```

**Tree.** The tree is drawn from the Scala definitions:
- links to the parent are green when proven;
- proposals have a dashed outline;
- nodes to review have an amber outline.

**Node.** In order:
1. the statement and the agent's reason ("proposed because");
2. the examples, with results against the contract and the implementation;
3. the link to the parent, side by side with the parent;
4. **the decision**: choose between alternatives (an accepted node can be
   replaced), accept a change after seeing its diff, or confirm that a node
   still holds after something above it or its code changed;
5. a box to **ask the agent** for something.

A reason is required for every decision. Decisions are recorded at once, with
no build.

**Inbox.** What waits for your decision, removed nodes to confirm, and the
agent's answers to your requests.

**Idea, Vocabulary, History.**
- `IDEA.md` is editable here.
- Vocabulary lists the open terms and what they mean.
- History lists every render, check and decision, with who made it.

## Agents

- **MCP server.** `.mcp.json` registers `frflow` (`bin/frflow mcp examples`).
  - Tools: `inbox`, `context`, `render`, `check`, `answer` and `scaffold`.
  - It has no tool for deciding. Decisions are the developer's, in the
    browser. An agent could still run the CLI's `accept` from a shell; only
    the skill tells it not to.
- **Skill.** `.claude/skills/frflow/SKILL.md` gives the agent its loop:
  1. Read the inbox.
  2. Propose alternatives with reasons and examples.
  3. Render and check.
  4. Answer the request.
  5. Remove the rejected nodes once the developer has decided.

## What is proven, checked, and trusted

- **Proven by Lean:** every link that is not vacuous, and so every node's root
  theorem. In short, the levels of the theory are consistent with each other.
  It does not say they are the right theory.
- **Checked by the examples:** that a contract means what its statement says,
  and that the implementation does what was decided, in those cases.
- **Enforced at run time:** every result of `service` meets the contract, or
  `ContractViolation` is raised. Each parameter is read once per call.
- **Decided by the developer:** every node, with its reasons. Examples, the
  diff and the side-by-side link are there to make that reading possible.
- **Trusted:**
  - the Scala-to-Lean translation;
  - `Int` read as unbounded;
  - parameters bound to the data the vocabulary says they mean;
  - every path to the data goes through `service`;
  - the ledger, a plain file under version control.
- **Not covered:**
  - properties over time or state, such as revocation or expiry;
  - feasibility of a contract beyond its examples;
  - effectful or asynchronous code, except a pure core behind `service`.

## Usage

Requirements: JDK 17+, sbt, and Lean 4.35.0 (`lake` on the PATH, or `FRFLOW_LAKE`).

```sh
sbt test                                  # unit tests, and Lean tests when lake is available
sbt "auth/run render"                     # Lean and the snapshot .frflow/kb.json, from the Scala definitions
sbt "auth/run check"                      # prove the changed links, record the results
sbt "auth/run status"                     # decisions, proofs and examples
sbt "auth/run context Authenticated"      # everything known about a node, for agents and people
sbt "auth/run accept Authenticated --by <name> --reason <text> [--reject ClientAsserted]"
sbt "auth/run confirm GrantBased --by <name> --reason <text> [--subtree]"
bin/frflow serve examples                 # the browser
bin/frflow mcp examples                   # the MCP server
```

Committed: the Scala, `IDEA.md`, `.frflow/ledger.json` and `lean/Proofs`.
Everything else is derived and git-ignored: generated Lean, check results,
the snapshot and the event log.

## Layout

```
lean/FrFlow/          the Lean side of the library: the frflow_auto tactic
core/                 the Scala library
  Model.scala         Opaque, Param, define
  Lift.scala          the macro: Scala lambdas to Lean
  Node.scala          nodes, examples, the knowledge base, service
  Decisions.scala     decision states and rules, shared by the CLI and the browser
  Ledger.scala        the decision record
  Generate.scala      Lean generation
  Workflow.scala      render, check, context, snapshot
examples/auth/        access control: idea, model, implementation, decisions
examples/crm/         multi-tenant CRM, the same
tools/                the browser server and UI, and the MCP server
bin/frflow            runs them
.claude/skills/frflow the agent skill
```
