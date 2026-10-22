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
- **Scale.** A large system grown by many agents over many sessions needs its
  theory to outlive every context window, its cross-cutting rules to hold
  everywhere, and the developer's attention spent on choices, not on every
  change.

## The method

The developer writes the idea in `IDEA.md`. The project's knowledge is a
**tree** of nodes, written in Scala:

- each **root** states one concern of the idea;
- each node below **specializes its parent**, one design decision at a time;
- **contracts** are what an implementation must satisfy on every call;
- **design** nodes record decisions that have no formal model, such as
  architecture or conventions; one that owns a directory is a **component**;
- **invariants** state a cross-cutting rule once ("no cross-tenant read"); each
  contract it applies to names it and keeps it.

| What is recorded | Where | Why it matters |
|---|---|---|
| the idea, and what it leaves out (`## Not modelled`) | `IDEA.md` | the limits of the theory are explicit |
| the vocabulary: what each open term means in the world | `Opaque("User", "a person who uses the system")`, `Param(..., means)` | how the model maps to the world |
| per node: statement, `why`, formal model | the Scala source | what holds at each level, and the reasoning behind it |
| per contract: examples (`expect` / `reject`) | the Scala source | what it means in concrete cases |
| per contract: what it does *not* promise, found mechanically | shown with the node | nobody believes it says more than it does |
| per node: who chose it, their reason, the alternatives rejected | `.frflow/ledger.json`, append-only | the decisions behind the design |
| cross-cutting rules, and the contracts that keep them | `Node.invariant`, `.holds(inv)(rule)` | one rule, checked everywhere it applies |

**The theory is built by deciding.** The developer works in the browser.
1. They ask for a next step.
2. The agent proposes one or more nodes, each with its reason and examples.
3. The developer compares them and chooses one, with a reason of their own.
4. The decision keeps that reason and the rejected alternatives, permanently.

The tree is decided from the root down. An agent picking up the work later
reads the whole record through `context`.

**The developer decides every choice; the agent settles what involves none.**
Roots, components, invariants, a node with alternatives beside it, a node that
introduces a term, and any change to what a node says are the developer's.
The agent may settle (`settle`) a mechanical node, one with no alternative
and no new term whose link holds and examples pass, and a change to the code
a node governs once the checks pass; it gives its reason, and the browser
lists what it settled for the developer to spot-check and endorse. Human
attention goes where the meaning is.

**Drift is caught by one rule: a decision binds a person's reason to the hash
of what they saw, and whatever moves under it puts the node back up for
review.** A node under review says why:

| Cause | What moved | Shown as |
|---|---|---|
| `self` | the node: statement, `why`, sources, examples (by value), the meaning of the terms it is the first to use, the definitions and types it uses, its parent, how its implementation is built; for a root, the idea and what is not modelled | a word-level diff against what was decided |
| `above` | the *meaning* of an ancestor: its statement, model, vocabulary, definitions (rewording a `why`, adding an example or editing the idea does not cascade) | the diff of the ancestor that moved |
| `code` | the code it governs: the files a contract's implementation refers to, a design node's (or component's) files, anything `.governing` names | a git diff against the code as it was decided; the files in full when first decided |
| `revisit` | the developer said a change above may affect it | the reason they gave |
| `merged` | two branches decided it, and a merge kept both | both decisions, in the history |
| `gone` | it was removed from the model | listed until the developer agrees |

A change of meaning cascades by itself. A change that does not, such as an
edit of the idea or of what is not modelled, may still break a reason written
below ("revisit if we add exports"). So when accepting a change, the browser
lists every decision below with its reason. The developer ticks those the
change may affect: they go back to review (`revisit`). The others still hold;
those that moved only because of this change are confirmed with the
developer's reason, by name, and leaving them all unticked is asked for
explicitly; the decisions left as they are are recorded as considered. The
reasons are where the conditions for revisiting are written; this is where
they are read. A root's change (an edit of the idea) lists every decision in
the knowledge base. An invariant's change reaches every contract that keeps
it, as a parent's does.

The developer **accepts** or **rejects**:
- accepting a proposal chooses it, and rejects the alternatives ticked;
  rejecting a proposal on its own chooses nothing instead;
- accepting a node under review says it holds as it now is. The reason it was
  chosen stays; when only something above it or its code moved, this is
  recorded as a confirmation;
- rejecting a node that was accepted (by choosing a replacement) puts what
  rests on it up for review (`above`); it stays drawn under the rejected node
  until the agent moves it under the replacement;
- what rests on a parent (a proposal, or a node whose parent moved) is decided
  after the parent; other reviews can be decided in any order;
- a reason, of a few words at least, is required for every decision, and a
  decision is refused if the node moved since the developer looked at it.

The levels are kept honest by Lean:
- **Every formal link is proven:** each node implies its parent.
- **Every formal invariant is kept:** each contract's post implies the rule it
  keeps, or the invariant is reported open.
- **A vacuous link fails, when `frflow_auto` shows it:** one where the parent
  holds whatever the node says.
- **A node that makes the root hold by itself fails, when `frflow_auto` shows
  it:** one where the root holds for every model of the node, whatever its
  spec says, because an `abs` or a substitution above decides it.
- **Assumptions about the world are shown:** a top-level condition (only) of a spec
  that never mentions the model constrains the world, not the system, and is
  listed with the node's limits.
- **An unsatisfiable node fails, when `frflow_auto` finds the contradiction:**
  a contradictory node would make every link below it hold and say nothing. A
  proof the agent wrote may be vacuous, or rest on a contradiction, in ways
  automation did not find, so the browser asks the developer to read such
  proofs.

Behaviour is kept honest by examples and run-time checks:
- **Examples** run against the contract and the implementation. An
  implementation that always returns the same value must fail one of them.
- **On every combination of the examples' inputs,** the implementation also
  runs, and a result that breaks the contract or an invariant it keeps fails
  like an example.
- **Each contract lists what it does not promise**, found mechanically: inputs
  it never looks at, or the fact that an empty result always satisfies it.
- **In production,** `service` checks every result against the contract and
  the invariants it keeps.

`status` and the browser also warn:
- when a committed version of the ledger, or the ledger now, changed or
  removed decisions recorded in the version it follows (the ledger only grows;
  a merge may interleave both sides' decisions); a commit that deletes it
  starts a new record, and is a warning until the developer acknowledges it;
- when a source file of any kind under `src/main` is governed by no node, or
  the model's file holds code other than the model (helpers, classes, methods
  on domain types, definitions no node uses): code that could change
  unnoticed;
- when a statement or reason names a node that was rejected or removed, and
  when a contract never reads a parameter its ancestors use;
- when `.frflow/checks.json` is committed (proofs come from running `check`).

`status` exits 1 unless every node is accepted, every formal link and
invariant proven (or decided by reading, where a node opted out), every
example passing, with no warning, so CI can require it. Proof results
(`.frflow/checks.json`) are local, so CI runs `check` before `status`. When two
branches decided the same node, resolve the ledger conflict by keeping both
sides' entries; the node comes back as `merged`, and is decided again.

## Large projects, built by agents

The method is meant to hold as a system grows to many roots, contracts and
components, built by agents across many sessions:
- **The theory lives in files, not in any context window.** Each agent reads
  the slice it needs with `context(node)`: the path from the root with every
  reason and rejected alternative, what moved, and the decisions below.
- **Before adding, find.** `find` names the nodes that govern a file or
  mention a concern, so an agent extends the theory instead of forking it.
- **Every file has an owner.** An implementation governs the files it refers
  to; components (design nodes owning directories) govern the rest; a file no
  node governs fails `status`. Inside a component, code is the agent's to
  change and settle; at its boundary (its contracts) the developer decides.
- **Cross-cutting rules are stated once.** An invariant names nothing below
  it; each contract it applies to keeps it, and is checked against it.
- **Attention follows meaning.** The developer is asked for choices and for
  changes in meaning; mechanical work is settled by the agent and listed for
  spot-checks; a change's effect below is shown as one list with the reasons
  it may touch.
- **Branches merge.** The ledger only grows; a node two branches decided comes
  back to be decided again.

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
| design | `parent.design(id, statement, why)(files*)` or `Node.design(...)`; a component when it owns a directory | none: decided and tracked; its files are what it depends on |
| invariant | `Node.invariant(id, statement, why)`; each contract keeps it with `.holds(inv)(rule)` | Lean: each contract's post implies its rule |

Any node can also govern extra files or directories with `.governing(paths*)`.

**Lean is the default; a node can opt out** with `formal = false` (on `root`,
`refine`, `instantiate` or `contract`). Its model stays Scala, and may use any
Scala; a contract's `post` still runs its examples and is still enforced by
`service`. Nothing is translated to Lean: the link reads "not formalized",
and the developer decides it by reading. Everything below an opted-out node
is out of Lean too, since there is nothing formal above it to prove against. Use it
where a proof costs more than it gives, or where the subset cannot say it
(state, time, effects); say why in `why`.

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
no build. Saving the idea starts a render. Render and check run the CLI
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
  - Tools: `inbox`, `context`, `render`, `check`, `answer`, `settle`, `find`
    and `scaffold`.
  - It has no tool for choosing. Choices are the developer's, in the browser;
    the agent settles only what involves none, and the developer spot-checks
    it.
  - **Decisions run on trust.** The CLI has no command for deciding either,
    but an agent with a shell could post to the local server or edit the
    ledger; only the skill tells it not to. Review the ledger's diff in git as
    you review code.
- **Skill.** `.claude/skills/frflow/SKILL.md` gives the agent its loop:
  1. Read the inbox.
  2. Propose alternatives with reasons and examples.
  3. Render and check.
  4. Answer the request.
  5. Remove the rejected nodes once the developer has decided.

## What is proven, checked, and trusted

- **Proven by Lean:** every formal link and kept invariant, and so every formal
  node's root theorem; links `frflow_auto` shows vacuous, and nodes it shows
  unsatisfiable, fail. A link decided by reading (`formal = false`) is not
  proven, and is shown as such. In short, the levels of the
  theory are consistent with each other. It does not say they are the right
  theory.
- **Checked by the examples:** that a contract means what its statement says,
  and that the implementation does what was decided, in those cases.
- **Enforced at run time:** every result of `service` meets the contract, or
  `ContractViolation` is raised. Each parameter is read once per call (a
  parameter bound to a lambda of up to three arguments answers each question
  once). `service` refuses to start if a parameter the contract reads is not
  bound.
- **Decided by the developer:** every node, with its reasons. Examples, the
  diff and the side-by-side link are there to make that reading possible.
- **Trusted:**
  - the Scala-to-Lean translation (it refuses what it cannot translate
    faithfully, such as a local name that shadows a parameter; division by
    zero is 0 in Lean and an exception in Scala);
  - `Int` read as unbounded;
  - parameters bound to the data the vocabulary says they mean (in examples, a
    parameter bound to a function is recorded by its source text);
  - that `abs` describes what the system really does with the model (shown
    side by side with the parent);
  - every path to the data goes through `service` (keep the wiring in a file
    a node governs);
  - code the agent settled, until the developer spot-checks it;
  - the ledger, a plain file under version control;
  - authored proof files, which Lean runs on your machine when checking: the
    filter on them is hygiene; the guarantee is the kernel replay and the
    axiom audit.
- **Not covered:**
  - properties over time or state, such as revocation or expiry;
  - feasibility of a contract beyond its examples, unless `frflow_auto` shows
    it is unsatisfiable;
  - effectful or asynchronous code, except a pure core behind `service`;
  - which files code really depends on: ownership is by file and directory,
    as declared; code outside `src/main` of the project, such as other sbt
    modules, is not seen;
  - patterns Lean would read differently from Scala are refused (matching on
    `true`/`false`, type tests); division by zero is 0 in Lean and an
    exception in Scala.

## Usage

Requirements: JDK 17+, sbt, and Lean 4.35.0 (`lake` on the PATH, or `FRFLOW_LAKE`).

```sh
sbt test                                  # unit tests, and Lean tests when lake is available
sbt "auth/run render"                     # Lean and the snapshot .frflow/kb.json, from the Scala definitions
sbt "auth/run check"                      # prove the changed links, record the results
sbt "auth/run status"                     # decisions, proofs and examples; exits 1 unless settled (CI)
sbt "auth/run context Authenticated"      # everything known about a node, for agents and people
bin/frflow serve examples                 # the browser
bin/frflow mcp examples                   # the MCP server
```

Committed: the Scala, `IDEA.md`, `.frflow/ledger.json` and `lean/Proofs`.
Requests to the agent (`.frflow/requests.json`) are a work queue and are not
committed: the agent's reasoning belongs in each node's `why`.
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
