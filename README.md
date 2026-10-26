# FrFlow

FrFlow builds a formal model of a program next to its code: a tree of statements that refine the program's purpose
step by step, down to the code. Lean proves every step. The developer decides every statement and signs the
decision.

FrFlow is written in Scala 3 and uses Lean 4.

## The opportunity, and the problem with agentic coding

Agentic AI has changed software engineering. Developers explore the solution space much faster and build products at
a much higher pace.

The volume of generated code and the way agents work also bring new problems. FrFlow, inspired by Nada Amin's talk
*Future of Programming* (Scala Days 2026), addresses two of them, which add risk and cost to agentic software
engineering:

1. **Lost theory.** Peter Naur argued that a program is the visible part of a theory its programmers hold: why it is
   built the way it is, and how it maps to the world. When agents write the code, nobody on the team builds that
   theory. The agent loses it too, when its context ends. A system nobody understands cannot be changed safely.
2. **Growing entropy.** A codebase that grows without a record of what it contains and why loses its integrity. Over
   time this leads to inconsistencies, and then to fundamental bugs and security vulnerabilities.

## The approach

FrFlow builds a formal, proven model of the software as a refinement tree:

1. Development starts from a small set of formal statements about the program: its purpose.
2. Each statement is refined into parts. Lean checks that the parts of a statement together imply it, and that
   invariants stated across the tree hold.
3. The last refinement is the code. It is written in one of two ways:
   - as a plain Scala function or service, with property-based tests whose shape and data are derived from its formal
     contract;
   - with FrFlow's monadic DSL, which compiles both to running code and to a Lean model that the proof uses.

The model sits next to the code and acts as its contract: an interface the code conforms to, stricter and more
expressive than a type signature.

Formal proofs of what software does used to cost too much to be practical for most projects. With coding agents
writing the proofs, thorough formal verification becomes viable, and worth exploring.

## How it addresses the problems

The refinement tree is the source of truth for what the program does, and the code is checked against it:

- **The theory is written down.** Each statement is one sentence in the domain's words, with the reason it holds and
  the formula Lean reads. A new developer, or a new agent session, reads from the repository why the system is the way
  it is.
- **The links are proven.** Lean proves each step from the code's contracts up to the purpose at the root.
- **Change is visible.** A change to the code, to a statement, or to a term a decision rests on brings every affected
  statement back to the developer, with the diff.

This makes it possible for a developer to take responsibility for, and sign off on, mission-critical software, even
when agents write parts of it.

FrFlow does not depend on AI. The AI-agent layer is optional and sits on top of the core. Building software this way
without an agent is a useful exercise: it makes confidence in the software's quality much easier to reach.

## A small app, step by step

A CRM that companies share: each company keeps its records, and shares some of them with other companies. Simplified
from `examples/crm`.

**1. The purpose.** One statement at the root, with the formula Lean reads:

```scala
val mayRead = define { (u: Term[Account], r: Term[CrmRecord]) => r.tenant === u.tenant || shares.contains(Share(r.id, u.tenant)) }

val sharedCrm = Node.claim("SharedCrm",
  "A user's search finds exactly the stored records of their company and those shared with it.",
  why = "Companies keep their own records and choose what to share."
)(forall((u: Term[Account], r: Term[CrmRecord]) => search(u).contains(r) === (store.contains(r) && mayRead(u, r))))
```

**2. Refinements.** The root splits into two claims; Lean proves that together they imply it.

```scala
val noCrossTenantRead = Node.claim("NoCrossTenantRead",
  "A search never returns a record the user may not read.",
  why = "The isolation every company relies on."
)(forall((u: Term[Account]) => search(u).forall(r => store.contains(r) && mayRead(u, r)))).under(sharedCrm)

val searchFindsAll = Node.claim("SearchFindsAll",
  "A search returns every stored record the user may read.",
  why = "A CRM that returns nothing would meet the isolation claim alone."
)(forall((u: Term[Account]) => store.forall(r => mayRead(u, r) ==> search(u).contains(r)))).under(sharedCrm)
```

**3. A contract.** What every call of `search` returns. Lean proves it gives both claims.

```scala
val searchContract = Node.contract(search)("SearchContract",
  "A search returns the stored records the user may read, and all of them.",
  why = "The two claims, for one call, so every result can be checked."
)((u, result) => result.forall(r => store.contains(r) && mayRead(u, r)) && store.forall(r => mayRead(u, r) ==> result.contains(r)))
  .under(noCrossTenantRead, searchFindsAll)
```

**4. The code.** Plain Scala, attached to the contract:

```scala
final class Records(db: Database):
  def search(u: Account): List[CrmRecord] =
    db.records.filter(r => r.tenant == u.tenant || db.shares.contains(Share(r.id, u.tenant)))

val knowledge = KnowledgeBase("Crm")(sharedCrm, noCrossTenantRead, searchFindsAll, searchContract)
  .implement(searchContract)(Records(db).search)
```

`check` proves steps 2 and 3 in Lean and tests `search` against the contract on stores it generates. The running
service checks every result. Each statement waits for the developer's decision, and comes back for review when it,
its parts, or the code under it change. Written with the DSL instead, as `Flow` over the database's model, the code
is proven too.

## The statements

| Kind | What it says | How it is checked |
|---|---|---|
| claim | a property of the system, in the domain's words | Lean proves it from its parts |
| definition | what a term of the vocabulary means here | decided |
| contract | what every call of an operation returns | Lean, from its parts above; the code below is proven or tested against it |
| assumption | what an outside system does | decided; checked at run time and against its model |
| invariant | a rule every operation in its scope keeps | Lean, for each contract in scope |
| design | an architecture choice with no formal content | decided; a change to the code it covers brings it back |

A statement can rest on several parents, so the tree is a directed acyclic graph with one root.

## Decisions

The developer accepts or rejects each statement, in the terminal or in a local web view. Each decision is signed with
the developer's key and kept in a ledger in the repository. When something a decision rests on changes, the statement
comes back for review with the diff. `status` exits with 1 while anything waits for a decision or is not proven, so CI
can gate on it.

## Using it

`bin/frflow PROJECT COMMAND` runs a project's command line. The screenshots are from `examples/keycloak`.

- `tree`: the graph from the root, with each statement's state and kind.

  ![bin/frflow keycloak tree](docs/img/cli-tree.png)
- `show NODE`: one statement, why it holds, its formula, where it sits, and its parts with what Lean proved.

  ![bin/frflow keycloak show NoUnauthorizedAccess](docs/img/cli-show.png)
- `review`: the statements waiting for a decision, each with what changed. Here the check that the user is still
  enabled was removed from the introspection code: three examples fail, and the proof of the code no longer goes
  through.

  ![bin/frflow keycloak review](docs/img/cli-review.png)
- `check`: render the model as Lean and prove it. `status`: the state of the whole project.

  ![bin/frflow keycloak status](docs/img/cli-status.png)
- `sbt "PROJECT/serve --as NAME"`: the same flow in a local web view: the graph, the statement under review with its
  diff, and the inbox. Decisions are signed as in the terminal.

  ![The web view](docs/img/web-view.png)

## With an AI agent

The agent layer (`modules/agent`) is enabled per project with `extensions = List(frflow.agent.Agent)`. The developer
describes the idea in a conversation; the agent asks what it needs, proposes the root and its refinements, writes the
proofs and the code, and answers the developer's questions about any statement. The developer decides. The agent's
rules are in [`.claude/skills/frflow/SKILL.md`](.claude/skills/frflow/SKILL.md).

## Getting started

You need JDK 17 or later, sbt, and Lean 4.35.0 installed with [elan](https://github.com/leanprover/elan), so that
`lake` is on the `PATH`.

```sh
git clone https://github.com/szymon-rd/fr-flow && cd fr-flow
bin/frflow auth tree                    # the smallest example; compiles on first use
bin/frflow keycloak check               # prove the keycloak example in Lean
bin/frflow keycloak show RealmAccess    # read its root
sbt "keycloak/serve --as NAME"          # the web view on localhost, deciding as NAME
```

`sbt "frflowInit NAME"` creates an empty project in `examples/NAME`. `sbt "frflowInitAgent NAME"` creates one with the
agent layer enabled.

## Examples

- `examples/auth`: access control by a table of grants. The smallest.
- `examples/keycloak`: realms, sign-in, token introspection and sign-out over HTTP. The sessions are proven to follow
  the history of requests.
- `examples/crm`: a multi-tenant CRM on SQLite with an HTTP API. Its expiry job is a flow over the database, proven
  from the database's model.
- `examples/sharing`: documents, folders and teams shared between people, with expiring shares, invitations, a trash,
  access requests, notifications and an audit log. Time, failures and concurrency are modelled.

## Proven, tested, assumed

Each part of the code is in one of three states, and `status` reports which:

| State | What it means |
|---|---|
| **proven** | written with the DSL; Lean proves it meets its contract |
| **tested** | plain Scala; tested against its contract on generated cases, and checked on every call at run time |
| **assumed** | an outside system, such as a database or the clock; its behaviour is a decided assumption, checked at run time and against its model on generated runs |

Everything above the code is proven from these. The assumptions are listed, decided and reviewed like any other
statement.

What is trusted:

- The assumptions the developer accepts, such as the model of a database the code talks to.
- FrFlow's translation of the model to Lean. The examples cross-check it by running the same model as Scala.
- For tested code: the generated cases and the run-time checks, which cover the inputs they reach, not every input.

## Inspiration

- Nada Amin, [*Future of Programming*](https://scaladays.org/session/future-of-programming/), keynote at Scala Days
  2026.
- Peter Naur, *Programming as Theory Building* (1985).
- Niklaus Wirth, *Program Development by Stepwise Refinement* (1971).
- Ralph-Johan Back's refinement calculus, and Carroll Morgan, *Programming from Specifications* (1990).
- Eric Evans, *Domain-Driven Design* (2003).
- Leonardo de Moura and Sebastian Ullrich, *The Lean 4 Theorem Prover and Programming Language* (2021).

## Documentation

- [docs/index.html](docs/index.html): tutorial, how-to guides, reference and troubleshooting.
- [docs/USAGE.md](docs/USAGE.md): commands, output and exit codes, what Lean proves, warnings, the web view, modules.
- [docs/DAG.md](docs/DAG.md): the design of the refinement graph.
