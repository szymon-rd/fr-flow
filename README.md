# FrFlow

FrFlow is a Scala 3 library for building software together with a formal model of it, proven in Rocq.

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

FrFlow proposes a way to build a formal, logically proven model of the developed software as a refinement graph. It
follows the method of stepwise refinement (Wirth, 1971) and the refinement calculus (Back, 1978; Morgan, 1990):

1. Development starts from a specification: a small set of core, formal statements about the program.
2. Then, gradually, each statement is refined. A refinement step replaces a statement with more concrete statements
   that together imply it. Every refinement step is a proof obligation, and Rocq checks it, so a statement can never
   contradict the one it refines, and Rocq also proves that the statements as a whole do not contradict each other.
3. The final refinement is the program's code itself. Its specification is declared on the code's own
   interfaces: a service is a trait, a `Declaration` of the trait is the value the claims speak of, and the claims
   are written through the trait's members. An implementation is then one of:
   - **Lifted**: a class that implements the trait, written as ordinary Scala. FrFlow compiles the class into the
     model from the TASTy the Scala compiler wrote for it, and the prover shows that it meets every claim, alone
     and among other calls ([docs/LIFTED.md](docs/LIFTED.md);
     [examples/links](examples/links/README.md): a link shortener proven to meet the claims on its three members
     and on how they relate).
   - **Assumed**: no implementation is given. The trait is known by the assumptions about it, as an outside
     system or a library is.
   - **Tested**: plain Scala, which FrFlow tests with property-based testing on generated cases, whose shape and
     data are driven by the statements about it.
   - Code in FrFlow's monadic DSL, which compiles both to executable code and to a model used in a strict proof.

The logical model sits alongside the code that performs the given functions, and acts as its contract: an interface
the code conforms to, albeit stricter and more powerful than has been usual for software.

Normally, developing formal proofs for the functions of software would be a costly and inefficient way to verify and
define software. However, with coding agents, this approach of thorough formal software verification has become viable
and should be explored.

## How FrFlow addresses problems of agentic coding

In essence, FrFlow makes sure that there is a view of the software that is correct by construction. The refinement
graph is the source of truth, and it is meant to be impossible to diverge from at the functional level.

Every refinement step is proven in Rocq, from the statements about a single function up to the core statements at the
root. When the code meets them, the core statements hold as well. Nobody has to take it on trust that a check
somewhere deep in the code really gives the property stated at the top.

This addresses both problems. The graph, with the reason each statement was accepted for, signed in its decision, is
the theory of the program, and it stays in the repository after the agent's context ends. And every change to the code
or to a statement brings the statements it affects back to the developer for review, with the diff, so the codebase
cannot drift away from its specification unnoticed.

**That makes it possible for a human developer to realistically take responsibility and sign off on mission-critical
software, even if its parts are developed by agentic AI.**

The value of FrFlow is not limited to agentic coding, and it does not need to be used with AI. I encourage the exercise
of building software with this approach, as it makes it much easier to achieve confidence about the quality of the
developed software.

## Example: a link shortener

A link shortener gives a URL a short code, tells where a code leads, and removes a code. Below is the core of the
example; the whole of it is in [`examples/links`](examples/links/README.md).

### The code

A service is an ordinary trait, with the members such a service has and nothing added for the proofs:

```scala
final case class Url(address: String) derives FrSpec
final case class Code(number: BigInt) derives FrSpec
final case class Link(code: Code, url: Url) derives FrSpec

trait Links extends Mutable:
  update def shorten(url: Url): Code
  def resolve(code: Code): Option[Url]
  update def remove(code: Code): Unit
```

Its specification is in its companion: a `Declaration` of the trait, which is the value the claims speak of, and the
claims, written through the trait's members. Each member has a contract, and most of them say how two members
relate:

```scala
object Links:
  val shortener = Declaration[Links]("the link shortener: the codes it has given and the URLs they lead to")

  val shortenIsIdempotent = Node.claim("Shortening a URL a second time gives the code it gave the first time " +
      "and changes nothing.")(
    forall((u: Term[Url]) => shortener.shorten(u).isIdempotent))

  val shortenedCodeResolves = Node.claim("The code a URL is given leads to that URL.")(
    forall((u: Term[Url]) => shortener.shorten(u).andThen(code => shortener.resolve(code)) === some(u)))

  val shortenKeepsExistingLinks = Node.claim("Shortening never changes where a code that leads somewhere leads.")(
    forall((u: Term[Url], c: Term[Code]) =>
      shortener.resolve(c).isDefined implies shortener.resolve(c).unchangedBy(shortener.shorten(u))))

  val removedCodeNotReissued = Node.claim("A code just removed is not given to the next URL shortened.")(
    forall((c: Term[Code], u: Term[Url]) => shortener.shorten(u).following(shortener.remove(c)) =!= c))
```

A call in a claim is made on the structure as it stands; `.in(state)` makes it on another state, `.after` is the
state it leaves, and `.result` what it gives. The shorthands above are built of those: `q.following(c)` is
`q.in(c.after)`, `c.andThen(r => d(r))` is `d(c).in(c.after)`, `q.unchangedBy(c)` is `q.following(c) === q`, and
`c.isIdempotent` is `(c.again === c) && (c.again.after === c.after)`, where `c.again` is `c.in(c.after)`.

An implementation is a class, as it would be written without FrFlow:

```scala
final class RetiringLinks(var issued: List[Link], var retired: List[Code]) extends Links:
  update def shorten(url: Url): Code =
    val held = issued
    val known = held.find(l => Issued.leadsTo(held, l.code) == Some(url)).map(l => l.code)
    val code = known.getOrElse(Code(Issued.above(held, retired)))
    if known.isEmpty then issued = Link(code, url) :: held
    code

  def resolve(code: Code): Option[Url] = Issued.leadsTo(issued, code)

  update def remove(code: Code): Unit =
    issued = issued.filter(l => l.code != code)
    retired = code :: retired
```

The model lists the claims, the parts each is proven from, and the class given for the trait:

```scala
val links: FrModel = FrModel("Shortener")(
  Links.shortenIsIdempotent, Links.shortenedCodeResolves, Links.shortenKeepsExistingLinks, // …
  Links.removeChangesOnlyThatCode,
  Links.removedCodeLeadsNowhere.refines(Links.removeChangesOnlyThatCode),
  Links.removeKeepsOtherCodes.refines(Links.removeChangesOnlyThatCode),
  Links.removedCodeNotReissued,
  Links.shortener.define(lifted[RetiringLinks]))
```

The examples state facts of the code at work, on objects of the class:

```scala
class LinksExamples extends FrFlowExamples(links):
  private val one = shortener.holding(RetiringLinks(List(Link(Code(0), home)), Nil))

  example("a removed code: it leads nowhere, and is not given again"):
    val removed = shortener.remove(Code(0)).in(one)
    (shortener.resolve(Code(0)).following(removed) is None) &&
      (shortener.shorten(home).following(removed).result is Code(1))
```

### From a class to a proof

`lifted[RetiringLinks]` is an ordinary call that runs when the model is built. It is a compiler, with no macro
and no second Scala compilation in it:

1. The Scala compiler writes, beside each class file, a `.tasty` file: the class as it was typed, bodies included.
2. FrFlow opens that file, walks each member's tree and builds the member's term: a function of the class's state
   (a record of its constructor's fields) and the member's inputs, which gives its result and, of an `update`
   member, the state after it. Scala it does not read is refused, with the file and line.
3. The prover's printer prints each term as a definition, and the prover shows it meets each claim that names the
   member.

A claim holds of the structure in every state, not only in those the class reaches from an empty one, so the class
must be right in all of them: a new code is a number above every code given and every code removed, not a counter
a state could hold below a code already given. A class that holds other services is proven from the claims on
them, not from their classes, and each `update` member is also compiled as its steps among other calls
(`amongOthers`): before each step but the first, the others may have left any state ([docs/LIFTED.md](docs/LIFTED.md)).

Rocq proves all seven claims of the example, each from a short proof by hand over shared lemmas on lists
(`rocq/Proofs/Shortener`); each of the two conditions the claims are stated under is shown possible, and Rocq shows
each of the three examples by running the generated definitions on the values it gives ([docs/ROCQ.md](docs/ROCQ.md)).

### How a change is caught

`bin/frflow links check` writes the model as Rocq, proves each node, and has the examples checked against the code
and against the claims. The class forgets to keep the codes it removes:

```diff
   update def remove(code: Code): Unit =
     issued = issued.filter(l => l.code != code)
-    retired = code :: retired
```

What removing leaves is no longer what the proofs rest on, so none of them goes through, and the example fails on
the code: removing code 0 and shortening a URL gives code 0 again.

```text
o removedCodeNotReissued: open
  not proven: it imports the shared lemmas, which are not proven (the error is theirs, not its own proof's)
    Proofs/Shortener/Lemmas.v:87: Lemmas_remove: In environment
…
Examples
  x a removed code: it leads nowhere, and is not given again  Rocq: the claims contradict it; the code does not hold it
```

A change to a claim instead (the shortener allowed to give a removed code again, say) proves again, but the claim
changed, so it goes back to the developer for review with the diff: only a signed decision accepts it.

## Statements

There are three kinds of statements, the nodes of the graph:

| Kind | Written | What it says | How it is checked |
|---|---|---|---|
| claim | `Node.claim(statement)(formula)` | a property of the system, in the words of its domain | Rocq proves it from the claims that refine it, or of the code it mentions; where that code is plain Scala, it is tested on generated cases |
| assumption | `Node.assumption(statement)(formula)` | what is trusted: the world outside the code, an outside system's promise, what comes from outside | decided by the developer; what Rocq takes as given, and plain Scala it is about is tested against it where it can be |
| design | `Node.design(statement)(files*)` | an architecture decision no proof covers | decided by the developer; a change to the files it governs brings it back |

Statements are about two kinds of values:

| Value | Written | What it is |
|---|---|---|
| Declaration | `Declaration[A](means)` | a word of the model: what statements speak of and code calls. One nothing defines is known only by what the statements say of it, such as `booked` |
| Structure | `Declaration[Trait](means)`, of a trait of the developer's | a value with members: a service, a store. Its members are called on terms as the trait declares them: `limits.authorise(p).result` is what the call gives, `.after` the structure after it, `.in(state)` the same from a given state, `limits.current` the structure as it stands, `.amongOthers(run => …)` every step of the call among other calls. A claim on a class that holds it asks it as the holder has it: `ledger.total.in(handler.handle(p).after)` |
| Definition | `d.define(…)` of a Declaration, listed in the model beside the nodes; or `define { … }`, declared and defined at once | a Declaration with a meaning, such as `book`: a class that implements a structure's trait (`d.define(lifted[Class])`, compiled from its TASTy and proven), a `define` (`d.define`, proven), plain Scala (`d.defineTested`, tested), or a value (`d.defineValue`, `d.provided`) |

They use two quantifiers: `forall`, every possible value, and `always`, every value of a type the code FrFlow covers
can produce (`always[T](x => …)`). A claim on a structure is said of the structure in every state.

A statement refines the statements it serves (`.refines`) and lists the assumptions it rests on (`.assuming`). A
statement can refine several others, and there can be several roots, so the statements form a directed acyclic graph.

## Proven, tested and assumed

The code at the bottom of the graph is in one of three states, and `status` reports which:

- **Proven** code is one of two things. A class that implements a structure's trait, lifted by its type
  (`limits.define(lifted[RecordedLimits])`): it is compiled from its TASTy as the model is built, and each member is
  proven to meet every claim on it, alone and among other calls. Or a `define` written in the DSL.
  [docs/LIFTED.md](docs/LIFTED.md) lists the Scala that is read.
- **Tested** code is plain Scala. It is tested against its claims with property-based testing on generated cases.
- **Assumed** code is known only by the assumptions about it, such as an outside system's search: Rocq takes them as
  given, and its Scala is tested against them. A structure with no class is known
  the same way (`pricing.provided`); a model that holds one is valid, and the prover does not build it yet.

Everything above the code is proven from these. Rocq is also asked that the statements can hold together: that
each condition a claim is stated under can be met, and, of the words no code defines, that some meaning makes the
statements about them hold. Where it shows neither, `check` says so; it is not taken as given.

Nothing is checked when the code runs: FrFlow is for testing before production and for proofs. A proof here does
not cover, and so trusts:

- The assumptions and the design decisions the developer accepted. A design node is decided, not proven: that
  each call of a store is one transaction, that a log delivers again what was not committed.
- FrFlow's reading of the code. The terms it compiles from a class's TASTy, and the Rocq it prints from them, are
  tested and not proven. `check` runs the examples on those terms and in Rocq; it does not run the class itself.
  FrFlow's own suite does, for classes that cover each kind of Scala it reads: each member is run on the JVM on
  drawn inputs, and the terms and the generated Rocq are held to what it gave (`AgreeRocqSuite`).
- How a class is read: its state its own (Scala's separation checking, where it is compiled), each call it makes
  of what it holds one step, other calls acting between the steps. Threads within a step, a call that fails, and
  time are not in the model.
- For tested code, the cases the tests reach.
- Rocq, with classical logic and extensionality as axioms; the Scala compiler and the JVM.

Rocq 9 is the prover that checks a project (`check`): the model is printed as Rocq, each module compiled after
those it imports, and what each proof rests on audited ([docs/ROCQ.md](docs/ROCQ.md)). [docs/ROCQ.md](docs/ROCQ.md) says what is
proven of each example and what is not yet.

FrFlow states safety properties: "eventually" is out of scope for now. Effectful programs written in the DSL
(`Flow`), state models and the clock were removed; a service's state is a structure's.

## Decisions

The developer accepts or rejects every statement, in the terminal or in a local web view. Each decision is signed with
the developer's key and kept in a ledger in the repository, and counts only when its key is on the project's list of
deciders, which the developer signs. When anything a decision rests on changes, the statement comes back for review
with the diff. `status` exits with 1 while anything waits for a decision or is not proven, so CI can gate on it.

## Using it

`bin/frflow PROJECT COMMAND` runs the command line of a project, on the terminal with colors and the interactive
review; `sbt "PROJECT/run COMMAND"` gives the same, plain.

- `tree` shows the graph from the roots, with each statement's mark, kind and state.
- `show NODE` shows one statement: what it says and why it was accepted, its formula, how it is checked, where it
  sits, its parts and the rules it uses, and what Rocq proved; `diff NODE` what moved since it was decided.
- `review` goes through the statements waiting for a decision, each with what changed; `inbox` lists them.
- `check` renders the model as Rocq, proves it and tests the code; `status` shows the state of the whole project, and
  `ci` does both for CI.

`sbt "PROJECT/serve --as NAME"` runs the same as a local web view, with the graph, the statement under review and its
diff, and the inbox. Decisions are signed the same way as in the terminal.

## With an AI agent

The agent layer (`modules/agent`) is enabled per project with `extensions = List(frflow.agent.Agent)`. The developer
describes the idea to the agent, which asks what it needs to know, proposes a README and the roots and their
refinements, writes the proofs and the code, and answers the developer's requests about any statement. The decisions
stay with the developer. The agent's rules are in [`.claude/skills/frflow/SKILL.md`](.claude/skills/frflow/SKILL.md).

## Getting started

You need JDK 17 or later, sbt, and Rocq 9 with `rocq` on the `PATH` (`opam install rocq-prover`).

```sh
git clone https://github.com/szymon-rd/fr-flow && cd fr-flow
sbt "frflowInit toy --as NAME"       # an empty project in examples/toy, NAME its first decider
sbt reload
bin/frflow toy status                # compiles on first use
sbt "toy/serve --as NAME"            # the web view on localhost, deciding as NAME
bin/frflow links status              # an example: links, auth, ox
```

`sbt "frflowInitAgent toy --as NAME"` creates one with the agent layer enabled. `sbt test` runs FrFlow's fast tests;
`sbt rocqTest` runs the ones that run Rocq end to end, the examples' among them.

## Examples

Each example is a project in `examples/<name>`: its statements and code in `src/main`, its examples in `src/test`,
its proofs by hand in `rocq/Proofs`, and its command line in `app`
(`bin/frflow <name> COMMAND`). No decision counts in any of them: `auth` keeps a ledger from an earlier shape of its
model, and `links` and `ox` have none.
FrFlow's own suites test them whole (`sbt rocqTest`).

- `links` is the example above: a link shortener, one service with three members, its claims on each and on how
  they relate, proven of its class.
- `auth` is access control by a table of grants, and the smallest example.
- `ox` states what holds of a scope's threads once Ox's `unsupervised` or `supervised` has completed, over the
  executions of Ox's own code ([its README](examples/ox/README.md)).

## References

- Nada Amin, [*Future of Programming*](https://scaladays.org/session/future-of-programming/), keynote at Scala Days
  2026.
- Peter Naur, *Programming as Theory Building* (1985).
- Niklaus Wirth, *Program Development by Stepwise Refinement*, Communications of the ACM 14(4), 1971.
- Ralph-Johan Back, *On the Correctness of Refinement Steps in Program Development*, PhD thesis, University of
  Helsinki, 1978; and Ralph-Johan Back and Joakim von Wright, *Refinement Calculus: A Systematic Introduction* (1998).
- Carroll Morgan, *Programming from Specifications* (1990).
- Eric Evans, *Domain-Driven Design* (2003).
- The Rocq Prover (formerly Coq), [rocq-prover.org](https://rocq-prover.org).

## Documentation

- [docs/USAGE.md](docs/USAGE.md) describes the DSL, the commands, their output and exit codes, what Rocq proves, the
  warnings, the web view and the modules.
- [docs/DAG.md](docs/DAG.md) describes the design of the refinement graph.
- [docs/LIFTED.md](docs/LIFTED.md) describes plain Scala compiled into the model (`lifted[Class]`, `FrSpec`,
  structures): what is read, what holds the Scala and the term to one meaning, and what is not built
  yet.
- [docs/ROCQ.md](docs/ROCQ.md) describes the prover: how a model reads in Rocq, how a check runs it, what is
  proven of the examples, and what is left.
- [docs/redesign/](docs/redesign/ARCHITECTURE.md) is the design record of the library as it was rebuilt, and the
  owner's decisions the sources cite.
