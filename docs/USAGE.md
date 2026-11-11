# Using FrFlow

The reference for the DSL, the command line and what it checks. The [README](../README.md) explains the idea;
[DAG.md](DAG.md) is the design of the graph; [redesign/ARCHITECTURE.md](redesign/ARCHITECTURE.md) is the design
record of the library, in full.

FrFlow is in two layers. [FrFlow (core)](#frflow-core) is the method and its tools: the graph, the proofs, the
decisions, the CLI and the web view, used by a developer with no AI. [With an AI agent](#with-an-ai-agent) is a layer
on top, which a project enables, for an agent that proposes the nodes and writes the code and proofs.

## FrFlow (core)

### Running

Requirements: JDK 17+, sbt, and Lean 4.35.0 (`lake` on the `PATH`, or `FRFLOW_LAKE`). `bin/frflow PROJECT COMMAND`
runs a project's CLI on the terminal, with colors and the interactive review, compiling with sbt on first use and
after a change; `sbt "PROJECT/run COMMAND"` runs it through sbt, plain. `--help` lists the commands. A project is
`examples/PROJECT`; FrFlow's own four (`rooms`, `auth`, `keycloak`, `crm`) are there too.

FrFlow's own tests: `sbt test` runs the fast ones (a few minutes); the ones that run Lean end to end (tagged `Lean`)
run with `sbt leanTest`; `sbt testAll` runs both. Per module, `sbt core/test`, `sbt project/test` and so on; eval's
is `sbt evaluation/test`, since `eval/…` is sbt's own command (it would evaluate the rest as Scala).

Run sbt and `bin/frflow` from the build's root (the directory holding `build.sbt`). A model records the files its
nodes, code and vocabulary are written in when it is compiled, relative to the directory the compiler runs in, and
the CLI makes them relative to the project's directory when it runs, from the directory it runs in; both are the
build's root under `bin/frflow`, `sbt "PROJECT/run …"` and `serve`. A run from another directory (an IDE's run
configuration, say) would place them wrongly: `status` would warn of the model's own files as ungoverned.

### Commands

| | command | what it does |
|---|---|---|
| read | `tree [NODE]` | the graph from the roots (or from NODE): each node's mark, kind, review state and statement |
| | `show NODE [--full]`, `diff NODE` | a node in about a screen (`--full`: all of it); what moved since it was decided |
| | `inbox`, `find WORDS\|PATH` | what waits for the developer, in the order to decide it; the nodes that govern a file, or mention some words |
| decide | `review` | decide what waits, node by node: `[a]ccept [r]eject [s]kip [v]iew [q]uit` |
| | `accept NODE... [--revisit NODE...]`, `reject NODE`, `confirm`, `revisit NODE`, `gone NODE` | one decision, with `-m REASON`; asked to confirm on a terminal, `--yes` without one |
| | `deciders --as NAME`, `rebase` | list your key as the project's first decider; accept the ledger as it reads now as where its history starts |
| prove | `render`, `check [NODE]`, `scaffold NODE` | write the Lean; prove each node and test its code, recording the results; stubs for what the last check left open |
| | `status`, `ci`, `export` | the tree, the warnings and the summary (exit 1 unless complete); `check` then `status`; the snapshot `.frflow/kb.json` |

`--as NAME` names who decides (default: `FRFLOW_AS`); `FRFLOW_ROOT` overrides the project's directory, and
`FRFLOW_SEED` the tests' seed (a number, or `fresh`). The commands that decide, and the web view, ask for it when
neither is set. The web view is not a command: it is an sbt task, `sbt "PROJECT/serve [--port N] [--as NAME]"`
([Web view](#web-view)).

### Starting a project

1. `sbt "frflowInit NAME --as YOU"` sets up an empty project in `examples/NAME`: a FrModel with no nodes, its main
   object, a class for its examples, its line in `build.sbt`, and, with `--as`, the deciders' list naming your key
   (`.frflow/deciders`, signed by it: commit it). Then `sbt reload`.
2. Write the root statements: a small set of claims, each one idea, in the domain's words, over `Declaration`s where
   the purpose is more general than the code.
3. Refine each into parts that together imply it, down to claims about the code, and give each `Definition` its
   meaning. `check` proves each step and tests the code; `review` decides each node, parents first.

A project's README is ordinary documentation: FrFlow neither reads nor tracks it. The decided statement of the
purpose is the roots and their refinements.

### Output and exit codes

On a terminal the output has colors and Unicode and fits the terminal's width: formulas, diffs and decisions wrap,
other lines are cut (`show --full` shows them whole). `--plain`, `NO_COLOR` or `TERM=dumb` turn this off. Off a
terminal (CI, agents, a pipe) the output is plain ASCII and no line is cut. `--json` on `check` and `status` prints
the result as JSON.

Each node's mark: `+` proven or tested, `x` fails, `o` not proven, `?` not checked yet, `-` nothing to prove, `!` to
decide.

Exit codes: 0 fine; 1 something is not accepted or proven, or a decision was refused; 2 a usage error or an unknown
node; 3 no Lean (`lake`).

### Statements

A model imports one facade, `import frflow.*`. There are three kinds of node (owner's decisions §15), each named by the
`val` it is assigned to:

| Kind | Written | Checked |
|---|---|---|
| claim | `Node.claim(statement)(formula)`; one with no parents is a root | proven in Lean from its parts (`complete`), or of the proven code it mentions (`impl`); tested where it mentions plain Scala |
| assumption | `Node.assumption(statement)(formula)` | trusted: the world outside the code, an outside system's promise, what comes from outside; Lean takes it as given, and the Scala it is about is tested against it where a case can be evaluated |
| design | `Node.design(statement)(files*)` | none: a decision about code no proof covers; a change to the files it governs brings it back |

Edges: `.refines(parents*)` makes a node a part of each parent (several parents, several roots: a directed acyclic
graph); `.assuming(assumptions*)` lists the assumptions its check rests on, which FrFlow derives and checks
(`PremiseMissing`, `PremiseNotNeeded`); `.replaces(other)` marks an alternative, so accepting one rejects the other.
A claim of `always` placed with `.refines` is a **rule** below the statement it serves, not a part of its step: Lean
has its rule of every value already, and `show` lists it under "Rules it uses". A node has no reason field: why it
holds is the reason given with its signed decision.

Statements are about two kinds of values:

| Value | Written | What it is |
|---|---|---|
| `Declaration` | `val booked = Declaration[List[Booking]]("the bookings made, as the world stands")` | abstract: known only by what the statements say of it; never called by code, a `define` or a program (`Stating` is asked for, which only statements, examples and a `stated` define's body give) |
| `Definition` | `val granted = Definition[(RoomBookings, Booking) => Boolean]("…")` | what code and programs use, of any type; it must get a meaning, once (`Undefined` otherwise) |
| `define { … }` | `val free = define { (bookings: Term[List[Booking]], request: Term[Booking]) => … }` | a Definition given its meaning on the spot, up to six inputs: a Lean `def`, run as Scala by the evaluator |
| `program { … }` | `val bookIfGranted = program { (request: Term[Booking]) => (for … yield …).atomically }` | a program given its meaning on the spot, its type `A => Flow[R]` |
| `stated { … }` | `val viewFollows = stated { (lib: Term[Library], p: Term[PersonId], d: Term[DocId]) => mayView(p, d) === letsView(lib, p, d) }` | a define whose body may apply a Declaration, so a statement can name a line over Declarations; used only in statements, as a Declaration is (a program, plain code or a `define` calling it does not compile); a Lean `def` taking the Declarations it applies, and the world last where one of them changes with it |

Quantifiers: `forall((x: Term[A]) => …)`, every possible value (to six variables); `exists((x: Term[A]) => …)`, some
value (to six variables; Lean's `∃`); and `always`, every value that the code FrFlow covers can produce:
`always[T](x => …)` of a type (every value of `T` that can be made), `always(stored)(s => …)` of a model's state
(every state it reaches; `always(a, b)((s, u) => …)` relates two). What always holds of a variable's type is a
premise below a `forall` and a conjunct below an `exists` (`∃ b, bookingsEndAfterStart b ∧ …`). An `always` is a
node's whole formula, one rule per node.

### Writing formulas

Formulas and proven code are terms: a `Term[A]` is an expression of type `A`, printed as Lean for the proofs and
evaluated as Scala for the examples and the tests. A domain type is a case class or an enum that `derives LeanType`.
Lambda parameters are annotated (`(b: Term[Booking]) => …`), so the term knows its type; FrFlow reads their names off
the lambda.

| Write | For | In Lean |
|---|---|---|
| `x === y`, `x =!= y` | equality (`==` between terms does not compile) | `=`, `≠` |
| `&&`, `\|\|`, `!`, `a implies b` | logic; `implies` is a word, so `a && b implies c` is `(a && b) implies c` | `∧`, `∨`, `¬`, `→` |
| `b.start`, `make[RoomBookings](room, bookings)`, `b.updated(_.end, e)` | a field, a record built from terms, a copy with one field changed | fields, `RoomBookings.mk`, `{ b with … }` |
| `when(c)(a).otherwise(b)` | a conditional on a term (a term has no truth value while the formula is built) | `if c then a else b` |
| `e.on[Event.Expired](at => …)` | a match on an enum, its cases named, `.type` for a case without fields | `match` |
| `let(v)(x => …)` | a value shared, named | `let x := v; …` |
| `some(x)`, `none[A]`, `o.getOrElse(d)`, `o.isDefined`, `o.forall(…)`, `o.exists(…)` | options | `Option` |
| `o.fold(d)(x => …)`, and as its fold: `o.map(…)`, `o.filter(…)`, `o.filterNot(…)`, `o.contains(x)`, `o.isEmpty`, `o.toList` | an option's value, or `d` | `match o with \| none => … \| some x => …` |
| `xs.forall(…)`, `exists`, `filter`, `map`, `foldLeft`, `contains`, `isEmpty`, `length`, `::`, `++`, `:+` | lists | `List` |
| `xs.pairwise(r)`, `xs.allDistinct` | `r` of every two elements, the earlier first; no element twice | `List.Pairwise`, `List.Nodup` |
| `m.get(k)`, `m.getOrElse(k, d)`, `m.updated(k, v)`, `s.contains(x)`, `s.union(t)` | maps and sets (not iterated) | `Map`, `Set` |
| `+`, `-`, `<`, `<=`, `>`, `>=` on `BigInt` | arithmetic; an `Int` literal is a `Term[BigInt]` where one is expected | `Int` |

A define is called by name (`covers(b, t)`) and passed where a function is expected (`held.pairwise(apart)`,
`xs.forall(isOpen)`). In plain Scala, `d.fn(env)` runs a define and `env(d)` reads a Definition's value.

### The World

A statement holds in every world the service reaches: the application at one moment, as the proofs see it, one field
per model's state. It is never named in a statement. What changes with it is read in the current world: a model's
state, `stored.current`; a Declaration (every Declaration may change with the World); a define whose body reads
state. A program applied in a statement is a run from the current world:

- `p(x).result` is what it returns (an `Either[E, R]` where `p` is declared `.failsWith[E]`, so a statement about it
  covers the runs that fail);
- `p(x).after` is the world it leaves, read with `stored.in(p(x).after)`;
- `p(x).ifSucceeds(r => …)` says what a run that succeeds gives, and is true of one that fails; `p(x).ifFails(e => …)`
  what a failed run does, true of one that succeeds (`p(x).ifFails(_ => p(x).changesNothing)`). Each is
  `p(x).result.fold(…)` with `True` on the other side, so Lean reads the same;
- beside a run, every world read is named: `t.current` for the world before it (`accepted(request).current`).

`t.isConstant`, of any value, says no run of any program from the current world changes it (where a condition holds:
`closed(room) implies bookingsOf(room).isConstant`, the condition read before the step). Of a Declaration, which no
code gives a value, it is an assumption: `Node.assumption("The opening hour never changes.")(openingHour.isConstant)`.
Two idioms: "a booking once made is never removed", `forall(b => stored.contains(b) implies
stored.contains(b).isConstant)`; "a count never goes down", `forall(n => n <= count implies (n <= count).isConstant)`.

What a statement may not say, each refused where it is written: an `always` inside a formula; a rule reading a
Declaration that changes with the World; two runs in sequence (a sequence is a program doing both); a value provided
where the code runs beside the World. FrFlow states safety properties: "eventually" is out of scope for now.

### Giving a Definition its meaning

| Written, on the FrModel | Code | Claims mentioning it are |
|---|---|---|
| `.implementProven(book)(bookIfGranted)` | a `program { … }` or a `define` | proven of the code in Lean |
| `.implementTested(granted)(env => (held, request) => …)` | plain Scala, given the other Definitions' values | tested on generated cases (1,000 by default) |
| `.implementTested(inRoom, add)(start = …, observe = …)(t => (t.inRoom, t.add))` | the plain Scala of a model's operations, over a store `start` makes from a state and `observe` reads back | proven on the model in Lean; the Scala tested against the model on generated runs |
| `.implementValue(trashKeeps)(BigInt(30 * 86400))` | a value | stated with the value |
| `.implementProvided(grants, sessions)` | a value given where the code runs | stated for every value provided |

A `define` or a `program` is its own meaning. `.withGenerator(gen.describedAs("…"))` gives the tests' cases of a type
(`Gen.oneOf`, `for` over generators); the values drawn meet every `always` on their type.

**Plain Scala, read.** `lifted { (a: A, b: B) => … }` is a Definition given its meaning where it is written, as a
`define` is, from an ordinary Scala function of one to four inputs: the compiler reads the function's body into the
term a `define` would build (a compile error at any Scala it does not read: state, effects, calls that can fail,
`Int` arithmetic, recursion), and the function stays the Scala it is (`noOverlap(a, b)` on values is a `Boolean`).
It may call other lifted functions, `inline def`s, and, where the project compiles with `-Yretain-trees`, ordinary
methods of the developer's code, whose bodies are read where they are called.

```scala
final case class Booking(room: String, start: BigInt, end: BigInt)
object Booking:
  given FrSpec[Booking] = FrSpec.derived[Booking].where(b => b.start < b.end)

val noOverlap = lifted { (a: Booking, b: Booking) => a.room != b.room || a.end <= b.start || b.end <= a.start }
val bookingsEndAfterStart = Node.assumption("Every booking ends after it starts.")(contractOf[Booking])
```

Every type of a value in it has an `FrSpec`: the type's `LeanType` with its contract, a rule over the value's
members written in Scala (`where`) or with the DSL (`whereStated`); `derives FrSpec` gives one with no contract. A
node states the contract (`contractOf[T]`, an `always[T]`). `lifted { noOverlap(x, y) }` of a closed expression is a
`Term[Boolean]`, an example's fact in plain Scala. `testing.Agreement` tests each lifted function's Scala against
its term on generated cases, and `testing.Vectors` gives Lean what the Scala gave as examples to decide; `check`
does not run them yet. [LIFTED.md](LIFTED.md) says what is read, and what holds the Scala, the term and the Lean to
one meaning. A service method that changes a store (a `caps.Mutable` class, under capture and separation checking)
is read by `updating { (service: S^, input: A) => service.method(input) }`, a function of the store's state, and by
`interleaving { … }(others)`, the same among other calls that keep the rely `others`. A service may hold several
stores or services; its companion then names its state (`type State = …`), and its calls of other services are
read as calls of their Definitions ([the payment stream](../examples/payments/README.md),
[the wallet](../examples/wallet/README.md)).

**An operation on a state** is a Definition of type `A => Flow[R]`, given its meaning in Lean by a `StateModel`, which
says what it does to the model's state, a field of the World:

```scala
object storedBookings extends StateModel[List[Booking]]("every booking stored, oldest first"):
  inRoom.means(room => state.get.map(stored => make[RoomBookings](room, stored.filter(b => b.room === room))))
  add.means(booking => state.update(stored => stored :+ booking))
```

`state.get`, `state.set(s)` and `state.update(f)` are the steps of a meaning. A model whose operations may fail is
`StateModel.failing[S, E](means, error)`: each call may fail with `error`, the world choosing which.
What the world outside does with a model is said of it, each as an assumption:

| Formula | Says |
|---|---|
| `stored.onlyCodeChanges` | nothing outside the code changes the state; the programs that do are derived from the code |
| `stored.initially(s => …)` | what the state starts in |
| `stored.atomic` | runs on it never interleave, and each call is one step against calls at once |
| `Clock.clockModel.schedule(other)((now, o) => …)` | the world moves the time only where the rule allows, given `other`'s state |

**An operation known only by assumptions** (`fetch.assumed` inside the model) has no meaning in Lean beyond what is
assumed of its runs (`forall(q => fetch(u, q).result.forall(…))`, `databaseModel.in(fetch(u, q).after) ===
databaseModel.current`). Lean takes it as an unknown function of its model's state, those assumptions as hypotheses;
its Scala is tested against them on the model's generated runs where a case can be evaluated, and is otherwise
"trusted, not tested", which `show`, `check` and `status` say. Its results are values from outside.

**Values from outside.** Statements are about values, never about a function's inputs. What comes from outside has a
type, and what is trusted of it is an assumption of `always` on that type
(`Node.assumption("Every booking ends after it starts.")(always[Booking](b => b.start < b.end))`). Every value covered
code makes or stores of that type is still proven to meet it, so an assumption cannot hide a bug in the code.

**In production**, nothing is checked: `knowledge.code(admit)(grants := table, sessions := tokens)` gives a
Definition's meaning as plain code calls it, and `knowledge.running[IO](storedBookings := table)` what programs run
with, each model's Scala bound, `run(bookIfGranted)(request)` running one.

### Programs

A program is one type, `Flow[R]`, written as a `for` comprehension over its steps; an operation applied is a step.
Lean reads the steps, and production folds them into any `F: Async`.

| Write | Does |
|---|---|
| `flow.atomically` | one transaction: no step of another run comes between its steps |
| `Flow.pure(t)`, `Flow.unit`, `.map`, `.as(t)`, `.void` | a value, no step |
| `Flow.when(c)(fa)`, `Flow.cond(c)(fa, fb)`, `Flow.ifM(fc)(fa, fb)` | a step or none, one of two, by a condition |
| `Flow.each(xs)(x => …)`, `Flow.collect(xs)(…)`, `Flow.fold(xs, z)((acc, x) => …)` | over a list, in turn |
| `Flow.parCollect(xs)(…)`, `Flow.parCollectN(n)(xs)(…)`, `(fa, fb).parTupled` | at once |
| `fa.race(fb)` | both at once, the loser cancelled when the winner finishes |
| `Flow.raise(e)`, `fa.handle[E](e => …)`, `fa.attempt[E]`, `fa.guarantee[E](fin)`, `Flow.bracket[E, R, A](acquire)(use)(release)` | errors and finalizers |
| `fa.timeout(Clock.now, seconds)`, `Flow.retry[E, A](Clock.sleep, waits)(fa)` | a time limit (`None` once it is past); a retry after each wait |

A program that can fail declares its error on its Definition: `Definition[Time => Flow[Unit]]("…").failsWith[E]`.
FrFlow checks the declared error against what the code may end in (`FailsWithDiffers`); a program over two error types
is refused. `p.changesNothing`, of a program declared to fail, says every model's state is as before.

**Time** follows Cats Effect's model. The clock is FrFlow's own model, `Clock.clockModel`, its state the time now in
seconds: `Clock.now` reads it, `Clock.sleep(d)` waits at least `d`, and `Clock.elapse(d)` is the world's own step
between runs, which no code calls. Steps of code take no time of their own; in Lean the world moves the time on by any
amount at each of the clock's steps and by at least `d` at a wait, and waits at once take the longest of them. Every
rule and `isConstant` reading the clock is asked to survive time passing (`cover_elapse`). In the tests the clock is
a virtual one, moved by `elapse` on generated runs.

**Concurrency.** Lean reads the sides of a step at once in turn; production interleaves their steps. `commute_<i>`
asks of each two steps, one of each side, touching a model in common that their two orders give the same results and
leave the same models, so what is proven of the reading holds of every interleaving (Lipton's reduction). A side that
may let an error out beside one that may fail or changes a model is refused. A race is read as the world's choice of
the winner, then the loser's steps until it is cancelled, then the winner's.

### What Lean proves

`check` writes the model's Lean under `lean/FrFlowGen/<Model>/` and builds it with `lake`. Each node's obligations:

| Obligation | Of | Says |
|---|---|---|
| `complete` | a claim with parts | its parts, with the assumptions it lists, imply it |
| `needed_<part>` | each part | the step needs it |
| `impl` | a claim mentioning proven code | the code meets it, its parts and the claims about what the code calls as hypotheses |
| `root_impl` | the roots | the code meets them, through the claims saying what each Declaration is |
| `cover_<program>` | an `always` about a store | every run of each program writing it, from a world meeting every rule, ends in one meeting it |
| `made_<maker>` | an `always[T]` | every value a proven define, program or operation makes of `T` meets it |
| `made_<code>_call_<i>` | proven code calling plain Scala | each argument meets the rules on its type, on every path to the call |
| `start_<node>` | an `always` about a store | the states it starts in meet it |
| `outside` | a claim of `always[T]` whose `T`s come from outside | what is assumed of them gives it |
| `commute_<i>` | a program with steps at once | each two steps that may interleave commute |
| `consistent_<i>` | each group of statements at the bottom sharing an open value | some meaning of every open value makes them all hold |
| `inhabited_<node>`, `satisfiable_<i>_<node>` | an `always`; a condition `A` in `A implies B` | some value meets it; it can hold |
| `example_<set>_<i>` | each example: the `i`th of its class (`example_GrantedExamples_0`), a try | for every meaning of what it mentions, the claims constraining them give its fact |
| `example_<set>_<i>_opposite` | each example, a try | the same claims give its negation: they contradict it |

The tries (`vacuous`, `restates`, `clash`, `unsat`, `idle`, `frozen`) look for a statement that says nothing, restates
its part, contradicts another, holds whatever is done, or a schedule that stops time; each is reported as shown or not shown. A step Lean does not
prove is "open", with Lean's errors; one refuted is "failed", with the case Lean confirms.

A proof Lean's tactics do not find is written by hand in `lean/Proofs/<Model>/<node>.lean`; `scaffold NODE` writes a
stub for each obligation the last check left open. Lemmas shared between proofs go in `lean/Proofs/<Model>/Lemmas.lean`.
Generated Lean is never edited.

**Consistency gates the proof.** A group not proven is a failure: the whole model's proof is red, and so is every
statement proven from parts over a Declaration while a group below it is not proven. Witnesses are derived where they
can be (an equation, a bound, a fixed value, proven code); otherwise the group is proven by hand
(`consistent_<i>` in a proof file). Tested Scala alone is evidence, not proof.

### Examples

Examples are ordinary tests beside the model, read by `check` and checked against the code and, in Lean, against the
claims:

```scala
class GrantedExamples extends FrFlowExamples(rooms):
  example("back to back: granted"):
    granted(RoomBookings("Oak", List(Booking("Oak", 9, 10))), Booking("Oak", 10, 11)) is true
```

`example(name, d := v)` sets a provided Definition's value; such an example is checked in Scala only. An example
whose values break a rule on their type is refused. Nothing depends on examples: the theory and its Lean are the same
without them. Each comes to one of three outcomes:

- `+` it passes: the code holds it, and Lean shows the claims give it (or a proof file proves it);
- `o` the claims do not decide it within the budget, and the code does not fail it: reported and counted apart
  ("Examples: 10/99 pass; 89 not decided by the claims"), no failure;
- `x` it fails: the code does not hold it, or Lean shows the claims contradict it (its `_opposite`), or shows both
  it and its opposite (the claims are inconsistent there): `check` and `status` exit 1.

A fact only about Declarations has no code to run: the claims giving it, it passes.

An example the claims do not decide is not wrong: leave it as it is (a proof of `example_<set>_<i>` in
`Proofs/<Model>/Whole.lean` decides it). Each class of examples is made with its constructor without arguments (an
`object`, as it is); `status` warns of each class among the test classes it cannot make, and why. It cannot tell
which model such a class is of (it cannot make it to ask), so a class of examples the tests make with arguments (a
parametrised set, for a variant of the model) turns `status` red: give it a constructor without arguments too, on
the model as written, or keep it out of the test classes `check` reads (a suite's own test sources, not the
model's). Two classes of one
model of one name are refused (their theorems would be one). In a project `init` made, the examples also run with `sbt PROJECT/test` (FrFlow's test framework,
which `init` adds). FrFlow's own four are not run that way: their model projects (`roomsModel`, …) have no test
framework, since testing's tests depend on them; their examples run in testing's `ExamplesSuite` and in each one's
`PortSuite` (`sbt test`).

### Decisions

The developer decides every node. Whoever writes a node proposes it; only a decision signed by a listed decider's key
accepts it. `.frflow/ledger.json` holds each decision: who, the reason, the alternatives rejected, the commit, a
signature, and the decision before it.

- **Who decides.** `.frflow/deciders` lists the keys whose decisions count, signed by a listed key, and is committed;
  a decision by a key not listed there, or not verified, does not count, and `status` says so. The key is kept
  outside the repository (`~/.config/frflow/signing.key`, or `FRFLOW_KEY`).
- **Order.** A node waits until what it rests on is accepted; a parent is decided before its parts, a premise before
  what assumes it.
- **Mechanical decisions.** A node under review whose own content did not change, that Lean proves again: one batch,
  `confirm`.
- **Refused.** A decision on a node that moved since the developer saw it; a reason of fewer than three words; code
  that fails a generated case, or is not tested since it moved; a decider not listed; a ledger whose committed
  history was rewritten (a listed decider runs `rebase`).

A decision binds the reason to the hash of what the developer saw. Whatever moves under it brings the node back, with
the cause:

| Cause | What moved |
|---|---|
| `self` | what the node says: its statement, its formula, the meaning of what it mentions |
| `above` | the meaning of what it rests on |
| `parts` | its list of parts |
| `code` | the code it governs: the files of its implementation, or of a design |
| `revisit` | the developer said a change elsewhere may affect it |
| `merged` | two branches decided it, and the merge kept both |
| `writers` | a new program started changing a store its rule is about |

Rewording a statement whose formula is unchanged does not cascade below; a change of meaning does. Accepting a change
lists the decisions below it that it acts on, and the developer marks those it may affect (`--revisit`).

### What is trusted, and the limits

Trusted: the assumptions the developer accepted; FrFlow's translation to Lean (cross-checked by the examples and by a
law that Lean decides each generated term as the evaluator does); for tested code, the cases the tests reach. Not
modelled: liveness ("eventually"), two runs in sequence in one statement, a deadline kept by a program running beside
the others (an open point), values inside a map, a set or a function reached by an `always[T]` (refused).

### Warnings

`status` exits 1 unless every node is accepted and proven, consistency is proven, and there is no warning. The
warnings:

- no signing key; `.frflow/deciders` not as committed; the ledger's base not committed; a decision that does not count;
- a source file governed by two nodes, or by none (the model's own files aside: where its nodes, its FrModel and
  the code given its Definitions are written, and a file holding only vocabulary, each Declaration, Definition,
  `define`, `program`, `StateModel` and domain type recording its name and file, and each helper whose result type is
  written `Term[…]` or `Flow[…]` (or a function returning one) counting as vocabulary; and a file holding only what a
  `program`'s body refers to and vocabulary); a governed file that does not exist (`show` marks it missing
  under the design's "Files it governs");
- a proof file of no node;
- consistency not proven; a store's start not proven to meet its rules;
- a node nothing checks; an assumption the generated runs cannot evaluate (trusted, not tested); a schedule over a
  model no program writes; a node that restates its part.

### CI

Committed: the Scala, `.frflow/ledger.json`, `.frflow/deciders`, `.frflow/ledger-base` (after a rebase), the agent
layer's records if used, and `lean/Proofs`; the rest is derived (`.frflow/checks.json`, `tests.json`, `kb.json`,
`lean/FrFlowGen`). CI runs `ci`, caching `.frflow/checks.json` and `lean/.lake`, so only what changed is proven again.
Run the tests a second time with a fresh seed, so a case the fixed seed never makes can still be found (a failing
case is kept in `.frflow/counterexamples.json`, to commit):

```
bin/frflow NAME ci
FRFLOW_SEED=fresh bin/frflow NAME ci
```

FrFlow's own CI (`.github/workflows/ci.yml`) runs the size budgets (`bin/budget.py modules examples`), `sbt test` and
`sbt leanTest`.

### Web view

`sbt "PROJECT/serve [--port N] [--as NAME]"` serves the developer's flow in a browser, from the project's main object
in a JVM of its own: the graph with each node's state, a node with its diff since it was decided, the inbox, and the
decisions with their reasons. It listens on localhost (port 8765 by default) and prints a link with a random token,
which every route asks for. A layer on top adds its routes, behind the same token, and its script.

The page is a client of the same API as the CLI (`FrFlowApi`), so a decision is signed and recorded as `accept`
records it, and the CLI can run beside it. Once the model's sources change, the page says so and refuses decisions
until it is restarted.

### Modules

One sbt project each, under `modules/`, each with its own top package (`frflow.<module>`) and its name as sbt id, but
`eval`'s, `evaluation` (`eval` is an sbt command); the module graph is in
`build.sbt`, and what each may name of another in `project/architecture.conf`, which core's `ArchitectureSuite` checks:

```text
   core ◄── dsl ◄── eval ◄── testing        (facade `frflow.*` in eval)
    ▲  ▲
    │  └── proof
    └───── decision
   wire ─► proof, decision, testing
   project ─► proof, testing, decision, wire
   api ─► project ;  cli, web ─► api ;  agent ─► cli, web
```

- `core`: names, types, the term algebras and their interpreters, the IR, statements, validation, checking,
  consistency.
- `dsl`: what a model is written in: terms, nodes, flows, state models, the FrModel, the macros; elaboration.
- `proof`: obligations, the Lean AST, the term printer, lowering, layout, reading Lean's output, the judges; the Lean
  library (`modules/proof/lean`).
- `eval`: the Scala meaning of terms and of plain code, examples, flows run on models, production's interpreter; the
  facade `frflow.*`.
- `testing`: generators, property tests, model tests, interleavings, the witness and refutation searches, the
  examples' test framework.
- `decision`: content, the ledger, the deciders, review, the rule of each command.
- `wire`: the files under `.frflow/` and the snapshot, with explicit codecs.
- `project` (package `frflow.project`): the imperative shell: the project's files, Lean, git, the keys and the
  ledger, each with a live and an in-memory interpreter; the analysis; check, status, decide and export.
- `api`: `Reading`, `Deciding` and `Proving` over a project, and the views; front ends see nothing else.
- `cli`, `web`: the command line (`FrFlowApp`, the composition root) and the web view.
- `agent`: the AI agent's layer, on top of `cli` and `web`. No other module depends on it.

FrFlow's examples are projects under `examples/<name>`, each in two sbt projects so FrFlow's suites can test it
with no cycle in the build: its model (`<name>Model`: `src/main`, its examples in `src/test`, its proofs in
`lean/Proofs`), which testing's tests depend on, and its command line (`<name>`, its main object in `app`). Each is
checked whole by its `PortSuite` (project's tests) against what the library before the rebuild recorded
(`reference/`), and rooms' walk-through by `WalkthroughSuite` (cli's tests).

## With an AI agent

The agent layer (`modules/agent`, package `frflow.agent`) adds what an agent working in the project needs: its
commands, the developer's requests to it, the conversation the idea comes from, and their parts of `inbox`, `show`,
`review`, `status` and the web view. It keeps its own files, `.frflow/requests.json` and `.frflow/conversation.json`;
the core does not read them. The agent's rules are in [`.claude/skills/frflow/SKILL.md`](../.claude/skills/frflow/SKILL.md).

### Enabling it

A project enables it on its main object, and depends on the module in `build.sbt` (`example(NAME)` does, by default;
`example(NAME, layers = Nil)` does not):

```scala
object toyCli extends frflow.cli.FrFlowApp(frModel, root = "examples/toy", extensions = List(frflow.agent.Agent))
```

`sbt "frflowInitAgent NAME --as YOU"` sets up a new project this way. The layer is an `Extension` of the core's: a
`CliExtension` (its commands, and what it adds to a view) and a `WebExtension` (its routes and script).

### Its commands

| | command | what it does |
|---|---|---|
| developer | `ask NODE TEXT`, `ask --idea TEXT`, `close REQUEST...` | ask the agent for a change; close an answer read |
| | `conversation` | what you told the agent, its questions with the answers it assumed, and yours |
| | `review` | also offers to ask the agent for a change instead of deciding |
| agent | `said TEXT`, `asked QUESTION --assume ANSWER`, `replied QUESTION TEXT` | record the conversation the idea comes from |
| | `context NODE` | everything on a node (`show --full`), with its requests |
| | `answer REQUEST\|NODE TEXT` | reply to a request, or tell the developer of work they did not ask for |

A node asked of the agent waits with the agent, not in the developer's queue, until it answers or the node changes.
A rejected node, and a revisit, are listed for the agent in `inbox`.

### Starting a project with the agent

1. `sbt "frflowInitAgent NAME --as YOU"` sets up an empty project with the agent layer.
2. The developer tells the agent the idea in chat. The agent asks what it needs, a few questions at a time, each with
   the answer it assumes, and records the conversation as it goes (`said`, `asked`, `replied`), in
   `.frflow/conversation.json`. It is a record, not a decision, and no file refers to it.
3. The agent drafts the project's README from the conversation and proposes the roots and their first parts. The
   developer decides each node; the README is ordinary documentation.

### In the web view

With the layer, the page lists the agent's open questions (answered in chat) and the requests, offers to ask the
agent for a change on a node or on the whole idea, and shows the nodes with the agent. Agents use the CLI, not the web
view.
