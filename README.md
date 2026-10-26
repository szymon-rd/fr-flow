# FrFlow

FrFlow is a Scala 3 library for building software together with a formal model of it, proven in Lean 4.

## The opportunity and the problem with agentic coding

Coding with agentic AI has massively changed software engineering. By using it, developers can explore the solution
space much faster, and build products at much higher velocity.

However, the massive volume of generated code and the nature of agentic coding introduce new challenges. This library,
inspired by the *Future of Programming* talk (Nada Amin, Scala Days 2026), identifies two core issues that introduce
significant risk and cost to the new, agentic software engineering process. Namely:

1. **Lost theory.** Peter Naur argued that a program is the visible part of a theory its programmers hold: why it is
   built the way it is, and how it maps to the world. When agents write the code, nobody on the team builds that
   theory. The agent loses it too, when its context ends. A system nobody understands cannot be changed safely.

2. **Increasing entropy.** A codebase that grows in size without proper tracking of its content and architecture
   suffers from a lack of integrity, which may eventually cause inconsistencies, and even fundamental bugs or security
   vulnerabilities.

## Proposed solution

FrFlow proposes a way to build a formal, logically proven model of the developed software as a refinement tree. It
follows the method of stepwise refinement (Wirth, 1971) and the refinement calculus (Back, 1978; Morgan, 1990):

1. Development starts from a specification: a set of core, formal statements about the program.
2. Then, gradually, each specification is refined. A refinement step replaces a statement with more concrete
   statements that together imply it. Every refinement step is a proof obligation, and Lean checks it, so a statement
   can never contradict the one it refines, and parallel statements are checked against the invariants they share.
3. The final refinement is the program's code itself. At that level, it can be developed in one of two ways:
   - As a standard Scala function or service, with a set of required property-based tests, whose shape and data are
     driven by its formally defined contract.
   - As an implementation in FrFlow's monadic DSL, which compiles both to executable code and to a Lean model, which
     is then used in a strict proof.

The logical model sits alongside the code that performs the given functions, and acts as its contract: an interface
the code conforms to, albeit stricter and more powerful than has been usual for software.

Normally, developing formal proofs for the functions of software would be a costly and inefficient way to verify and
define software. However, with coding agents, this approach of thorough formal software verification has become viable
and should be explored.

## How FrFlow addresses problems of agentic coding

In essence, FrFlow makes sure that there is a view of the software that is correct by construction. The refinement tree
is the source of truth, and it is meant to be impossible to diverge from at the functional level.

Every refinement step is proven in Lean, from the contract of a single function up to the core statements at the
root. When the code meets its contracts, the core statements hold as well. Nobody has to take it on trust that a check
somewhere deep in the code really gives the property stated at the top.

This addresses both problems. The tree, with the reason written next to each statement, is the theory of the program,
and it stays in the repository after the agent's context ends. And every change to the code or to a statement brings
the statements it affects back to the developer for review, with the diff, so the codebase cannot drift away from its
specification unnoticed.

**That makes it possible for a human developer to realistically take responsibility and sign off on mission-critical
software, even if its parts are developed by agentic AI.**

The value of FrFlow is not limited to agentic coding, and it does not need to be used with AI. I encourage the exercise
of building software with this approach, as it makes it much easier to achieve confidence about the quality of the
developed software.

## A small app, step by step

Let's build a part of a CRM that several companies share. Each company keeps its own records, and can share some of
them with other companies. This is a simplified version of `examples/crm`.

**1. The specification.** We start with one statement at the root. It says what a search returns, in words and as a
formula that Lean reads:

```scala
val mayRead = define { (u: Term[Account], r: Term[CrmRecord]) => r.tenant === u.tenant || shares.contains(Share(r.id, u.tenant)) }

val sharedCrm = Node.claim("SharedCrm",
  "A user's search finds exactly the stored records of their company and those shared with it.",
  why = "Companies keep their own records and choose what to share."
)(forall((u: Term[Account], r: Term[CrmRecord]) => search(u).contains(r) === (store.contains(r) && mayRead(u, r))))
```

**2. A refinement step.** We refine the root into two statements, one for isolation and one for completeness. Lean
proves that together they imply the root:

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

**3. A contract.** We state what every single call of `search` must return. Lean proves that it gives both statements
above:

```scala
val searchContract = Node.contract(search)("SearchContract",
  "A search returns the stored records the user may read, and all of them.",
  why = "The two claims, for one call, so every result can be checked."
)((u, result) => result.forall(r => store.contains(r) && mayRead(u, r)) && store.forall(r => mayRead(u, r) ==> result.contains(r)))
  .under(noCrossTenantRead, searchFindsAll)
```

**4. The code.** Finally, we write the implementation in plain Scala and attach it to the contract:

```scala
final class Records(db: Database):
  def search(u: Account): List[CrmRecord] =
    db.records.filter(r => r.tenant == u.tenant || db.shares.contains(Share(r.id, u.tenant)))

val knowledge = KnowledgeBase("Crm")(sharedCrm, noCrossTenantRead, searchFindsAll, searchContract)
  .implement(searchContract)(Records(db).search)
```

Now `check` proves steps 2 and 3 in Lean, and tests `search` against its contract on stores it generates. The running
service checks every result as well. The developer accepts each statement, and when the code or any statement changes
later, the affected statements come back for review. Had we written `search` in the DSL, as a `Flow` over a model of
the database, it would be proven too.

## Statements

There are six kinds of statements:

| Kind | What it says | How it is checked |
|---|---|---|
| claim | a property of the system, in the words of its domain | Lean proves it from the statements that refine it |
| definition | what a term of the domain means in this system | decided by the developer |
| contract | what every call of an operation returns | Lean proves the statements above from it; the code below is proven or tested against it |
| assumption | what an outside system, such as a database, does | decided by the developer, and checked at run time |
| invariant | a rule that every operation in its scope keeps | Lean, for every contract in its scope |
| design | an architecture decision with no formal content | decided by the developer; a change to the code it covers brings it back |

A statement can refine several others, so the tree is in fact a directed acyclic graph with one root.

## Proven, tested and assumed

The code at the bottom of the tree is in one of three states, and `status` reports which:

- **Proven** code is written in the DSL, and Lean proves that it meets its contract.
- **Tested** code is plain Scala. It is tested against its contract on generated cases, and checked on every call at
  run time.
- **Assumed** code is an outside system, such as a database or the clock. Its behaviour is an assumption the developer
  decides, and it is checked at run time and against its model on generated runs.

Everything above the code is proven from these. What is left to trust is the assumptions the developer accepted,
FrFlow's translation of the model to Lean (which the examples cross-check by running the same model as Scala), and,
for tested code, the inputs the tests and run-time checks actually reach.

## Decisions

The developer accepts or rejects every statement, in the terminal or in a local web view. Each decision is signed with
the developer's key and kept in a ledger in the repository. When anything a decision rests on changes, the statement
comes back for review with the diff. `status` exits with 1 while anything waits for a decision or is not proven, so CI
can gate on it.

## Using it

`bin/frflow PROJECT COMMAND` runs the command line of a project. The screenshots below are from `examples/keycloak`.

`tree` shows the graph from the root, with the state and the kind of each statement.

![bin/frflow keycloak tree](docs/img/cli-tree.png)

`show NODE` shows one statement: what it says and why, its formula, where it sits, and the statements that refine it,
with what Lean proved.

![bin/frflow keycloak show NoUnauthorizedAccess](docs/img/cli-show.png)

`review` goes through the statements waiting for a decision, each with what changed. Here, the check that the user is
still enabled was removed from the introspection code, so three examples fail and the proof of the code no longer goes
through.

![bin/frflow keycloak review](docs/img/cli-review.png)

`check` renders the model as Lean and proves it, and `status` shows the state of the whole project.

![bin/frflow keycloak status](docs/img/cli-status.png)

`sbt "PROJECT/serve --as NAME"` runs the same flow as a local web view, with the graph, the statement under review and
its diff, and the inbox. Decisions are signed the same way as in the terminal.

![The web view](docs/img/web-view.png)

## With an AI agent

The agent layer (`modules/agent`) is enabled per project with `extensions = List(frflow.agent.Agent)`. The developer
describes the idea to the agent, which asks what it needs to know, proposes the root and its refinements, writes the
proofs and the code, and answers the developer's questions about any statement. The decisions stay with the developer.
The agent's rules are in [`.claude/skills/frflow/SKILL.md`](.claude/skills/frflow/SKILL.md).

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

`sbt "frflowInit NAME"` creates an empty project in `examples/NAME`, and `sbt "frflowInitAgent NAME"` creates one with
the agent layer enabled.

## Examples

- `examples/auth` is access control by a table of grants, and the smallest example.
- `examples/keycloak` has realms, sign-in, token introspection and sign-out over HTTP. Its sessions are proven to
  follow the history of requests.
- `examples/crm` is a multi-tenant CRM on SQLite with an HTTP API. Its expiry job is a flow over the database, proven
  from the database's model.
- `examples/sharing` shares documents, folders and teams between people, with expiring shares, invitations, a trash,
  access requests, notifications and an audit log. Time, failures and concurrency are modelled.

## References

- Nada Amin, [*Future of Programming*](https://scaladays.org/session/future-of-programming/), keynote at Scala Days
  2026.
- Peter Naur, *Programming as Theory Building* (1985).
- Niklaus Wirth, *Program Development by Stepwise Refinement*, Communications of the ACM 14(4), 1971.
- Ralph-Johan Back, *On the Correctness of Refinement Steps in Program Development*, PhD thesis, University of
  Helsinki, 1978; and Ralph-Johan Back and Joakim von Wright, *Refinement Calculus: A Systematic Introduction* (1998).
- Carroll Morgan, *Programming from Specifications* (1990).
- Eric Evans, *Domain-Driven Design* (2003).
- Leonardo de Moura and Sebastian Ullrich, *The Lean 4 Theorem Prover and Programming Language* (2021).

## Documentation

- [docs/index.html](docs/index.html) has a tutorial, how-to guides, the reference and troubleshooting.
- [docs/USAGE.md](docs/USAGE.md) describes the commands, their output and exit codes, what Lean proves, the warnings,
  the web view and the modules.
- [docs/DAG.md](docs/DAG.md) describes the design of the refinement graph.
