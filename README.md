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
| per contract: what it does *not* promise, found mechanically | shown with the node | nobody believes it says more than it does |
| per node: who chose it, their reason, the alternatives rejected | `.frflow/ledger.json`, append-only | the decisions behind the design |
| the developer's requests and the agent's answers | `.frflow/requests.json` | the trade-offs discussed on the way |

**The theory is built by deciding.** The developer works in the browser.
1. They ask for a next step.
2. The agent proposes one or more nodes, each with its reason and examples.
3. The developer compares them and chooses one, with a reason of their own.
4. The decision keeps that reason and the rejected alternatives, permanently.

The tree is decided from the root down. An agent picking up the work later
reads the whole record through `context`.

**Drift is caught by one rule: a decision binds a person's reason to the hash
of what they saw, and whatever moves under it puts the node back up for
review.** A node under review says why:

| Cause | What moved | Shown as |
|---|---|---|
| `self` | the node: statement, `why`, sources, examples (by value), the meaning of the terms it is the first to use, the definitions and types it uses, its parent, how its implementation is built; for a root, the idea and what is not modelled | a word-level diff against what was decided |
| `above` | the *meaning* of an ancestor: its statement, model, vocabulary, definitions (rewording a `why`, adding an example or editing the idea does not cascade) | the diff of the ancestor that moved |
| `code` | the code it governs: a contract's implementation (its package directory, subdirectories included) or a design node's files | a git diff against the code as it was decided |
| `revisit` | the developer said a change above may affect it | the reason they gave |
| `gone` | it was removed from the model | listed until the developer agrees |

A change of meaning cascades by itself. A change that does not, such as an
edit of the idea or of what is not modelled, may still break a reason written
below ("revisit if we add exports"). So when accepting a change, the browser
lists the decisions below with their reasons, and the developer ticks those
the change may affect: they go back to review (`revisit`). The reasons are
where the conditions for revisiting are written; this is where they are read.

The developer **accepts** or **rejects**:
- accepting a proposal chooses it, and rejects the alternatives ticked;
  rejecting a proposal on its own chooses nothing instead;
- accepting a node under review says it holds as it now is. The reason it was
  chosen stays; when only something above it or its code moved, this is
  recorded as a confirmation;
- one acceptance can also confirm everything below that moved only because of
  it, as long as each node's parent is accepted;
- a reason, of a few words at least, is required for every decision.

The levels are kept honest by Lean:
- **Every link is proven:** each node implies its parent.
- **A vacuous link fails:** one where the parent holds whatever the node says.
- **An unsatisfiable node fails, when `frflow_auto` finds the contradiction:**
  a contradictory node would make every link below it hold and say nothing. A
  proof the agent wrote may rest on a contradiction automation did not find,
  so the browser asks the developer to read such proofs.

Behaviour is kept honest by examples and run-time checks:
- **Examples** run against the contract and the implementation. An
  implementation that always returns the same value must fail one of them.
- **Each contract lists what it does not promise**, found mechanically: inputs
  it never looks at, or the fact that an empty result always satisfies it.
- **In production,** `service` checks every result against the contract.

`status` and the browser also warn:
- when any committed version of the ledger, or the ledger now, changed or
  removed decisions recorded before it (the ledger only grows; a commit that
  deletes it starts a new record, visibly);
- when a source file is governed by no node: code that could change unnoticed.

`status` exits 1 unless every node is accepted, proven and passing, with no
warning, so CI can require it.

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
  "Sessions and grants are loaded into memory, in one process.", why = "One service decides access; the tables fit in memory."
)("src/main/scala/auth/Server.scala")

val knowledge = KnowledgeBase("Auth", idea = "IDEA.md")(noUnauthorizedAccess, authenticated, grantBased, decisionContract, inMemorySessions)
  .implement(decisionContract)(SessionStore(grants.value.toSet, sessions.value).decide)

// Production (Server.scala): the registered implementation, every result checked against the contract.
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

`examples/crm` does the same for a multi-tenant CRM. (The example ledgers
were written by an agent, to show the method; in a real project only the
developer decides.)

## The node kinds

| Kind | Written as | Proof |
|---|---|---|
| root | `Node.root[M](id, statement, why)(spec)` | none: it is the statement |
| refine | `parent.refine[M2](id, statement, why)(abs, spec)` | Lean: `spec m → parent.spec (abs m)`, and not vacuous |
| instantiate | `parent.instantiate[M2](id, statement, why)(T := of[X], p := ...)` | none: the generic results apply |
| contract | `parent.contract[A, B, R](id, statement, why)(post).examples(...)(...)` | Lean: the contract implies the parent |
| design | `parent.design(id, statement, why)(files*)` or `Node.design(...)` | none: decided and tracked; its files are what it depends on |

Any node can also govern extra files or directories with `.governing(paths*)`.

The building blocks:
- **The domain** is Scala case classes and enums. They must keep structural
  equality.
- **The macro** translates node lambdas to Lean. Anything it does not support
  is a compile error.
- **Proofs.** Links are proven by `frflow_auto`. Failing that, the agent writes
  a proof in `lean/Proofs/<KB>/<NODE>.lean`:
  - it states exactly `Obl.link`;
  - it may contain only a few commands (no metaprograms, attributes or other
    imports);
  - its module is replayed through the Lean kernel, and its axioms are
    audited.

## The browser: where decisions are made

```sh
bin/frflow serve examples     # http://127.0.0.1:8765
```

**Tree.** The tree is drawn from the Scala definitions:
- links to the parent are green when proven;
- proposals have a dashed outline;
- nodes to review have an amber outline.

**Node.** In order:
1. the statement and its `why`;
2. the examples, with results against the contract and the implementation,
   and what the contract does not promise;
3. the link to the parent, side by side with the parent;
4. **the decision**:
   - choose between alternatives (an accepted node can be replaced), or
     reject a proposal;
   - or, for a node under review, see what moved (a word diff, the diff of
     the ancestor that moved, or the code's git diff) and accept it, ticking
     the decisions below that the change may affect;
5. a box to **ask the agent** for something.

A reason is required for every decision. Decisions are recorded at once, with
no build. Saving the idea needs no build either. Render and check run the CLI
through `sbt --client` (see `frflow.json`), so they take seconds once the sbt
server is up; `sbt --client shutdown` stops it.

**Inbox.** What waits for your decision, removed nodes to confirm, and the
agent's answers to your requests.

**Idea, Vocabulary, History.**
- `IDEA.md` is editable here.
- Vocabulary lists the open terms and what they mean.
- History lists every decision, read from the ledger.

## Agents

- **MCP server.** `.mcp.json` registers `frflow` (`bin/frflow mcp examples`).
  - Tools: `inbox`, `context`, `render`, `check`, `answer` and `scaffold`.
  - It has no tool for deciding. Decisions are the developer's, in the
    browser.
  - **Decisions run on trust.** An agent with a shell could still run the
    CLI's `accept`, or post to the local server; only the skill tells it not
    to. Review the ledger's diff in git as you review code.
- **Skill.** `.claude/skills/frflow/SKILL.md` gives the agent its loop:
  1. Read the inbox.
  2. Propose alternatives with reasons and examples.
  3. Render and check.
  4. Answer the request.
  5. Remove the rejected nodes once the developer has decided.

## What is proven, checked, and trusted

- **Proven by Lean:** every link that is not vacuous, from a node that is not
  unsatisfiable, and so every node's root theorem. In short, the levels of the
  theory are consistent with each other. It does not say they are the right
  theory.
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
  - every path to the data goes through `service` (keep the wiring in a file
    a design node governs);
  - the ledger, a plain file under version control;
  - authored proof files, which Lean runs on your machine when checking: the
    filter on them is hygiene; the guarantee is the kernel replay and the
    axiom audit.
- **Not covered:**
  - properties over time or state, such as revocation or expiry;
  - feasibility of a contract beyond its examples, unless `frflow_auto` shows
    it is unsatisfiable;
  - effectful or asynchronous code, except a pure core behind `service`;
  - code an implementation reaches outside its package directory, unless
    governed explicitly (`status` lists source files no node governs).

## Usage

Requirements: JDK 17+, sbt, and Lean 4.35.0 (`lake` on the PATH, or `FRFLOW_LAKE`).

```sh
sbt test                                  # unit tests, and Lean tests when lake is available
sbt "auth/run render"                     # Lean and the snapshot .frflow/kb.json, from the Scala definitions
sbt "auth/run check"                      # prove the changed links, record the results
sbt "auth/run status"                     # decisions, proofs and examples; exits 1 unless settled (CI)
sbt "auth/run context Authenticated"      # everything known about a node, for agents and people
sbt "auth/run accept Authenticated --by <name> --reason <text> [--reject ClientAsserted] [--revisit ID,ID] [--subtree]"
sbt "auth/run reject ClientAsserted --by <name> --reason <text>"
bin/frflow serve examples                 # the browser
bin/frflow mcp examples                   # the MCP server
```

Committed: the Scala, `IDEA.md`, `.frflow/ledger.json`, `.frflow/requests.json`
and `lean/Proofs`. (sbt splits commands at `;`, so avoid it in a reason given
on the command line.)
Everything else is derived and git-ignored: the generated Lean, the check
results and the snapshot.

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
  Git.scala           the code a decision saw, code diffs since, the ledger's history
examples/auth/        access control: idea, model, implementation, decisions
examples/crm/         multi-tenant CRM, the same
tools/                the browser server and UI, and the MCP server
bin/frflow            runs them
.claude/skills/frflow the agent skill
```
