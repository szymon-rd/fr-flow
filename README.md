# FrFlow

FrFlow is a tool and a method for building software with AI agents without
losing track of what the software is for. The agent writes the code and a tree
of small statements that explain it. Lean proves that the statements fit
together and that the code meets them. You decide every statement, and you see
it again when it changes.

FrFlow is written in Scala 3 and uses Lean 4.

## The problem of using AI for coding

- **Lost Theory.** Peter Naur argued that a program is the visible part of a
  theory its programmers hold: why it is built the way it is, and how it maps
  to the world. When agents write the code, nobody on the team builds that
  theory. The agent loses it too, when its context ends. A system nobody
  understands cannot be changed safely.
- **Drift.** Each change an agent makes can move what the system does a little
  away from what was intended. Each step looks reasonable on its own. Reviewing
  large generated diffs does not catch it, because the reviewer has no record
  of the intent to compare against.

## Formal refinement agentic flow

1. You write `IDEA.md`: the purpose of the system, in prose.
2. The agent proposes a root: one statement that says the purpose exactly,
   both what users can do and what must never happen.
3. The agent refines the root into parts, in the words of your domain:
   claims, contracts on operations, assumptions, definitions of terms, and
   design decisions. Parts have parts of their own, down to the code. The
   result is a DAG.
4. FrFlow translates the DAG to Lean and proves that the parts of each node
   imply it, that the code meets its contract, and that the root follows from
   the code and a short list of trusted assumptions.
5. You accept or reject each node, in the terminal or in a local web view.
   Each decision is signed and kept in a ledger with your reason.
6. When something changes, every node it affects comes back for review, with
   a diff of what changed.

How this addresses the two problems:

- **The theory is written down.** Each node is one sentence with a `why`, and
  you decided it. A new developer, or a new agent session, can read from the
  repository why the system is the way it is.
- **The links are proven.** You do not have to trust that a contract on one
  endpoint really gives the property stated at the root. Lean checks each step.
- **Drift shows up for review.** A change to code, to a statement, or to a term
  that a decision rests on puts that node back in your queue, with the diff.

This costs extra work: you read and decide nodes, and the agent writes
proofs. That work goes to the places where using AI is risky: the intent, and
whether the code still matches it.

What stays trusted: the assumptions you accept (for example, that the store
returns what it stored) and FrFlow's translation from Scala to Lean.

## Inspiration

- Nada Amin, [*Future of Programming*](https://scaladays.org/session/future-of-programming/),
  keynote at Scala Days 2026.
- Peter Naur, *Programming as Theory Building* (1985). The source of the Lost
  Theory problem.
- Niklaus Wirth, *Program Development by Stepwise Refinement* (1971). A
  program grows from its purpose in small, explained steps.
- Ralph-Johan Back's refinement calculus, and Carroll Morgan, *Programming from
  Specifications* (1990). Each refinement step is an obligation to prove.
- Eric Evans, *Domain-Driven Design* (2003). Nodes use the ubiquitous language
  of the domain, and each term is defined once.
- Leonardo de Moura and Sebastian Ullrich, *The Lean 4 Theorem Prover and
  Programming Language* (2021). The prover behind every check.

## How it works

Nodes are Scala values. This is the root of `examples/keycloak`, a small
Keycloak-like authentication server, and one of its two parts:

```scala
val realmAccess = Node.claim("RealmAccess",
  "A realm's application accepts a token as a user's, with the user's roles, exactly when the user signed in to that realm and got the token, has not signed out with it since, and is still enabled.",
  why = "...")(
  forall((r: Realm.T, t: Token.T) => forall((u: User.T) =>
    (accepted(r, t) == Some((u, rolesOf(r, u)))) == (signedIn(r, u, t) && enabled(r, u)))))

val noUnauthorizedAccess = Node.claim("NoUnauthorizedAccess",
  "A token is accepted only as a user who signed in to that realm with it, has not signed out since and is still enabled, and only with that user's roles.",
  why = "The safety half of the purpose: whatever an application is told about a token must be true of a sign-in that still stands.",
  idea = "No unauthorized access")(
  forall((r: Realm.T, t: Token.T) => accepted(r, t).forall(a =>
    signedIn(r, a._1, t) && enabled(r, a._1) && a._2 == rolesOf(r, a._1))))
  .under(realmAccess)
```

The sentence is what you decide. The formula is what Lean reads. Lean proves
that `NoUnauthorizedAccess` and its sibling `SignedInAreAccepted` together give
`RealmAccess`. Further down, the contract `Introspect` states what one call of
the introspection endpoint must return, and the Scala function that implements
it is proven to meet it. The running server also checks every result against
the contract.

## Using it

`bin/frflow PROJECT COMMAND` runs a project's CLI. The screenshots are from
`examples/keycloak`.

**1. See the tree.** `tree` shows the DAG from the root: each node's status,
its kind, and its statement.

![bin/frflow keycloak tree](docs/img/cli-tree.png)

**2. Read a node.** `show NODE` gives one node in about a screen: what it
says and why, the formula, where it sits, and its parts with what Lean proved.

![bin/frflow keycloak show NoUnauthorizedAccess](docs/img/cli-show.png)

**3. Review what changed.** Here an agent removed the check that the user is
still enabled from the introspection code. `review` puts the contract back in
front of you with the diff: three examples fail, and the proof of the code no
longer goes through. You accept it, skip it, or ask the agent about it; the
agent sees the question in its inbox.

![bin/frflow keycloak review](docs/img/cli-review.png)

**4. Check the state.** `status` exits 1 while anything waits for a decision
or is not proven, so CI can gate on it.

![bin/frflow keycloak status](docs/img/cli-status.png)

**5. Or use the browser.** `serve` runs the same flow as a local web view: the
graph, the node under review with its diff, and your inbox. Decisions are
signed the same way as in the CLI.

![The web view](docs/img/web-view.png)

The agent has its own commands (`inbox`, `context`, `check`, `scaffold`,
`answer`) and rules, in
[`.claude/skills/frflow/SKILL.md`](.claude/skills/frflow/SKILL.md).

## Getting started

You need JDK 17 or later, sbt, and Lean 4.35.0 installed with
[elan](https://github.com/leanprover/elan), so that `lake` is on the `PATH`.

```sh
git clone https://github.com/szymon-rd/fr-flow && cd fr-flow
bin/frflow auth tree                    # the smallest example; compiles on first use
bin/frflow keycloak check               # prove the keycloak example in Lean
bin/frflow keycloak show RealmAccess    # read its root
bin/frflow keycloak serve --as NAME     # the web view on localhost, deciding as NAME
```

The examples:

- `examples/auth`: access control by a table of grants. The smallest one.
- `examples/keycloak`: realms, sign-in, token introspection and sign-out over
  HTTP. The sessions are proven to follow the history of requests.
- `examples/crm`: a multi-tenant CRM on SQLite with an HTTP API.

## More

- [docs/USAGE.md](docs/USAGE.md): the commands, output and exit codes, what
  Lean proves, warnings, starting a project, the web view, modules, and
  measurements.
- [docs/DAG.md](docs/DAG.md): the design.
- [.claude/skills/frflow/SKILL.md](.claude/skills/frflow/SKILL.md): the
  agent's rules.
