---
name: frflow
description: >-
  Run as /frflow to start a new system from an idea (the agent sets everything up), or to continue one. Develop a
  system with FrFlow: a small set of root statements (the idea's purpose, kept concise) refined by a DAG
  of small statements in the domain's words, each proven in Lean from its parts and decided by the developer. Use
  when turning an idea into roots, proposing or changing nodes, introducing domain types and values, adding
  examples, answering the developer's requests, proving a step, or giving code its meaning; or when the work touches
  `Node.claim`, `Node.assumption`, `Node.design`, `Declaration`, `Definition`, `define`, `stated`, `program`,
  `forall`, `exists`, `always`, `FrModel`, `FrFlowExamples`, `.refines`, `.assuming`, `.replaces`, `implementProven`, `implementTested`,
  `implementValue`, `implementProvided`, `withGenerator`, `Flow`, `StateModel`, `onlyCodeChanges`, `initially`,
  `atomic`, `.assumed`, `.failsWith`, `.current`, `.in`, `.after`, `.result`, `.ifSucceeds`, `.ifFails`,
  `isConstant` or `Clock`.
---

# Developing with FrFlow

The developer tells you the idea in chat; you ask what you need, record the conversation, and draft the project's
README from it. Then you write Scala nodes: a small set of roots, kept concise (one idea each), and below them parts
that together prove them, down to claims about the code. Lean proves each step; the developer decides every node. The
README explains the method, `docs/USAGE.md` is the reference, `docs/DAG.md` the design.

These rules are the agent layer's (`frflow.agent`), on top of FrFlow's core. A project uses it when its main object
names it, `FrFlowApp(Name.model, root = "examples/NAME", extensions = List(frflow.agent.Agent))`; without it, `said`,
`asked`, `replied`, `conversation`, `ask`, `close`, `context` and `answer` are not there, and `inbox` lists no
requests, and `wait` is not there. Do not add it to a project whose developer set it up without the layer.

## Starting a project: the conversation

1. **Set up: yours, all of it.** The developer only starts `claude` and runs `/frflow` (this skill), then tells the
   idea. Do the rest without asking them to run anything:
   - the name: a lowercase word from the idea (`payments`); who decides: `git config user.name`, lowercased, unless
     they say otherwise;
   - a signing key, only if there is none at `FRFLOW_KEY` or `~/.config/frflow/signing.key`: make it once
     (`mkdir -p ~/.config/frflow && chmod 700 ~/.config/frflow`, then
     `k=$(openssl genpkey -algorithm ed25519); { echo "$k" | openssl pkey -outform DER | base64 -w0; echo; echo "$k" |
     openssl pkey -pubout -outform DER | base64 -w0; echo; } > ~/.config/frflow/signing.key; chmod 600 …`), and say
     so. Never read, copy or use the key yourself: it signs the developer's decisions, which stay theirs;
   - `sbt "frflowInitAgent NAME --as WHO"`, then `sbt --client reload`: an empty FrModel in `examples/NAME`, with the
     agent layer;
   - commit `examples/NAME/.frflow/deciders`, and only that file (`git add` it alone): FrFlow reads who decides from
     git history, so no decision counts until it is committed. Say that you did;
   - **ask how they will decide** (AskUserQuestion): in the web view, which you start, or in the CLI. For the web
     view, start `bin/frflow-web NAME --as WHO` in the background and give them the link it prints (the same across
     restarts): it rebuilds and restarts itself whenever a source changes, and the open page draws each node you add
     as it arrives. For the CLI, they decide with `bin/frflow NAME review`.
2. **Let the developer tell the idea**, in their own words, as long or short as they like. Record it verbatim:
   `said TEXT` (each message that tells the idea or corrects it). Do not write files yet.
3. **Ask only what you cannot assume.** Never ask what any engineer takes for granted (a payment system never
   creates or loses money, never overdraws, never applies a payment twice): state it as an assumption and build it
   in; the developer rejects a node with a comment if it is wrong. Ask at most a few questions, each with the answer
   you assume, so the developer can agree or correct it:
   "Can a company share a record with another? I assume yes, only the owner can, until a date." Ask only where the
   answer changes the roots or the first split: who the users are, what they can do, what the system keeps,
   what comes from outside and what is trusted of it, what is out of scope. Record each before asking it:
   `asked QUESTION --assume ANSWER`; record each answer as said: `replied QUESTION TEXT`. Stop when the roots can be
   stated; ask later questions when a node needs them, the same way.
4. **Restate the purpose in a sentence or two** ("A user finds exactly …") and ask the developer to confirm or
   correct it in chat. It becomes the roots.
5. **Draft the README** from the conversation, in the developer's words where possible: what the system is for, what
   users do, what must never happen, and what is not modelled. It is ordinary documentation: FrFlow does not read
   it, no node refers to it, and nothing in it refers to the conversation's questions.
6. **Then propose the roots**, and nothing below them yet. Where a node needs something the developer has not said,
   ask (step 3) instead of guessing. The reason a node holds is the developer's, given when they decide it: put your
   rationale in your `answer`, not in the node. Then wait for their decision (Proposing and waiting, below).

`conversation` shows what is recorded.

## Rules

1. **You propose; the developer decides.** Never edit `.frflow/ledger.json` or `.frflow/deciders`, decide for the
   developer, use their signing key, or run `accept`, `confirm` or `rebase` for them. Setting a project up is yours
   (Starting a project, step 1): the key made once if there is none, `init`, the deciders' list committed. Record
   the conversation only as it happened: never a reply the developer did not give. If `status` says a decision does
   not count, tell the developer.
2. **One statement per node**, one sentence in the developer's domain words; the formula says exactly that sentence.
   No concepts glued with `&&`: two ideas are two nodes, and what always holds is an `always` of its own.
3. **A part is never a restatement**, nor a fact that follows from definitions (a lemma of the proof): it is a
   decision that could have gone otherwise, or the claim about the code.
4. **2 to 5 parts per parent, as a rule.** More asks for an intermediate node.
5. **The roots are the promises, stated once, never synonyms** (Choosing the nodes, below): what users can do, with
   its exact effect, and each thing that must never happen, directly over the system's state and operations. A
   `Declaration` and the node saying what it is in the code only where the purpose is more general than the code
   (rooms' `bookedAfterIsStored`).
6. **Below the promises comes the rule**: each operation's one specification, split at most into what it does and
   what it refuses; then the design decisions; then the code.
7. **Introduce the domain as it is needed**: a domain type (a case class or an enum deriving `LeanType`) where the
   idea needs one, a `Declaration` where a concept is known only by what is said of it, a `Definition` where code
   provides it. Every Declaration and Definition says what it means and where its value comes from.
8. **What comes from outside has a type of its own**, and what is trusted of it is an assumption of `always` on that
   type. Never state an assumption about a function's inputs.
9. **Offer real alternatives**: the second `.replaces` the first; say the trade-off in your `answer`.
10. **Never weaken a node to make a proof or a test go through.** A false step means a part is wrong or missing; a
    failing generated case means the code is wrong, or the claim as decided is. If the idea or a decided node is
    wrong, say so.
11. **Never edit generated Lean** (`lean/FrFlowGen/`). Lean you write goes only in `lean/Proofs/<Model>/`.
12. **Every source file is governed by one node**: the claim whose code it is, or a design node (production wiring,
    the call to `model.code` or `model.running`, goes in one).
13. **Say what is not modelled** (in the README, and in your `answer`), and name the waiting nodes that are
    mechanical.
14. **Names.** A node's id is its `val`'s name, as are a Declaration's and a Definition's; ids are unique and
    distinct from every type and value. A `val` named after a Lean word (`decide`, `max`, `id`, `holds`) is refused;
    one named after a facade name (`after`, `result`, `when`, `always`) hides it. To rename a node, change its val
    and move its proof file; `.replaces(old)` links the two.
15. **Changes.** A change of meaning reviews what rests on the node; a change to governed code reviews the node:
    say why what rests on it still holds.

## Choosing the nodes

A node is a decision that could have gone otherwise. The tree is a funnel of such decisions, each level answering
one question about the level above; it is not the same properties copied down layer by layer. Choosing the nodes is
the hard part of the work; take the time.

**The levels**

1. **The system**: its name and what it is in a sentence or two, `FrModel("Payments", "Users hold accounts … and pay
   each other.")(…)`. The web view draws it as the root; it is not a claim, and nothing checks it.
2. **The promises (what)**: what its users can rely on, one root each: what they can do, with its exact effect (so
   that doing nothing does not meet it), and each thing that must never happen. Each could be otherwise (an overdraft
   could be allowed), which is why the developer decides it.
3. **The rule (by what behaviour)**: the one specification of each operation that delivers the promises: "Paying
   makes a payable payment, and changes nothing otherwise", as one or two nodes (what it does, what it refuses).
   Every promise hangs from it; the tree narrows here.
4. **The design decisions (how)**: only real choices: how the state is kept, what is trusted of the world outside
   (assumptions), what the state always holds, which mechanism a step uses.
5. **The code**: proven or tested against the rule and the decisions.

**The tests of a node**, before proposing it

- **Could it be decided otherwise?** What follows from definitions alone ("applying a payment keeps the total") is
  a lemma of the proof (`lean/Proofs/<Model>/Lemmas.lean`), never a node: there is nothing in it to decide.
- **Is it said once?** A property is stated at the level it is promised at. Below it, it is proven, never restated
  about another object (`othersUntouched` of the ledger, then again of `applied`).
- **Is it its parent, more concretely?** A part speaks of what its parent speaks of, with less freedom, or names the
  one decision that gets there. A part that needs a new concept: that concept is the decision, or the part is wrong.
- **Is there a gap to bridge?** State the promises directly over the system's state and operations
  (`books.in(pay(p).after)`). Use a `Declaration`, and the node saying what it is in the code, only where the
  purpose is more general than the code; where it is not, "the ledger is what the store holds" is a synonym.
- **Can it be decided in one read?** One invariant per node: one sentence, and a formula as short as the sentence
  (one equation or one implication, on one line), without opening a define. If not, split it, or name the concept.
- **Does the level stand alone?** Read a level's nodes by themselves: together they say everything the system
  promises at that level, and none follows from the others.

**Predicates**

- A long chain of conditions or effects is a concept of the domain: define it once, in the domain's words (`payable`:
  asked by the owner, positive, covered, to another account, not made before; `made`: the amount moved and the
  payment recorded), with a Scaladoc saying what it means, and state what holds of it:
  `payable(l, p) ⇒ made(l, after, p)`.
- A predicate names a concept, never a node. `accepted(p) === allowed(ledger, p)` only renames the node's own
  content, which then hides in the define: a synonym, and nothing for the developer to judge.

**Assume the obvious.** Never ask the developer to confirm what any engineer takes for granted (a payment system
never creates money); state it as a node, and let the developer reject it with a comment if it is wrong.

**The shape to expect**: several promises, one rule, a few decisions, the code. Many nodes each refining many
others, the same sentence at two levels, or a node that only renames another, mean the tree is copying properties
down instead of deciding.

## Proposing and waiting

Work in small steps the developer decides as they come: the roots first, then the parts of one accepted node at a
time (its first split, 2 to 5 parts), down to claims about code, the code itself, and a green `check`.

1. Write the step's nodes, add them to `FrModel(...)`, `render` and `check`. **Prove before you hand over, always**:
   every node you propose is proven (by FrFlow's automation or by your proof in `lean/Proofs/<Model>/`) or tested
   before the developer is asked to decide it; `check` shows nothing open on it. If a proof needs something nobody
   has stated (an invariant, an assumption about the world), that is part of the proposal: propose it in the same
   step, proven too. A node you cannot prove is not ready: fix it, or say what is wrong with it; never hand over an
   open obligation with a promise to prove it later.
2. Tell the developer in one or two lines what you proposed and why (the trade-off, what is left open).
3. **Wait**: run `bin/frflow NAME wait` in the background (Bash `run_in_background`). It ends when the developer
   accepts, rejects (with a reason) or sends back a node, or asks for something, and prints what moved; you are woken
   then. Do not poll, and do not propose the next step before it ends. If it ends with nothing (`--minutes`, 30 by
   default), run it again.
4. On what it reports:
   - **accepted**: refine the next accepted node that is not yet proven from parts or code (step 1).
   - **rejected, with a reason**: propose what the reason asks for in its place (`.replaces(old)` when it is an
     alternative), under the same parents; remove the rejected node, move what was under it, then wait again.
   - **revisit**: propose a change, or `answer NODE TEXT` why it still holds.
   - **a request**: the loop below.
5. Done when every node is accepted, every Definition has its meaning, `check` is green and `status` exits 0. Then say
   so, with what is not modelled.

## The loop

1. `inbox`: requests, rejected nodes (who rejected each and why), the summary.
2. For each request, read `context NODE`, and `find` where the change belongs. Place a new statement **under the
   lowest nodes it helps prove, as a part**. Extend what exists; do not add a near-duplicate.
3. Write the proposal and its examples, add it to `FrModel(...)`, then `render` and `check`. Fix failing examples
   first, then the steps.
4. `answer REQUEST TEXT`: the proposals, the trade-off, what is left open.
5. For a rejected node: if its reason asks for something, propose a node in its place that does it, under the same
   parents. Then remove the rejected node, move what was under it under the node chosen, and drop its name elsewhere.
6. When the developer asks to revisit a node, propose a change, or `answer NODE TEXT` why it still holds.

## Tools

`bin/frflow <project> COMMAND` from the repository root (`sbt "<project>/run COMMAND"` works too, slower). Piped, the
output is plain ASCII and not cut; `--json` on `check` and `status` prints JSON. `--help` gives the rest.

| command | use |
|---|---|
| `inbox` | Start here: requests, clean-up, waiting decisions, open questions, the summary. |
| `said TEXT`, `asked QUESTION --assume ANSWER`, `replied QUESTION TEXT`, `conversation` | Record the conversation the idea comes from; show it. |
| `context NODE` | Everything on a node (`show NODE --full`), with its requests. |
| `tree [NODE]`, `show NODE`, `diff NODE` | The DAG; a node in about a screen; what moved since it was decided. |
| `find WORDS\|PATH` | The nodes that govern a file, or mention some words. |
| `render` | Rebuild from the Scala; elaboration errors and the model's problems come back here. |
| `check [NODE]` | Prove what changed, test the code, evaluate the examples. Slow. A `timeout` is not a failure: run it again. |
| `status` | The tree, the summary and the warnings; exits 1 unless the FrModel is complete. |
| `scaffold NODE` | Stubs in the node's proof file for what the last check left open. |
| `answer REQUEST\|NODE TEXT` | Reply to a request, or tell the developer of work they did not ask for. |
| `wait [--minutes N]` | Block until the developer decides or asks; print what moved. Run it in the background. |

`ci` is `check`, then `status`. Exit codes: 0 fine; 1 not complete, or refused; 2 a usage error; 3 no Lean.

## The core concepts

Three kinds of nodes, two kinds of values, two quantifiers (the owner's decisions §15). There is nothing else: no
contract, invariant, model or definition node, no boundary, no `Program`. Never work around them.

- **Nodes.** `Node.claim(statement)(formula)`: proven from its parts or of the proven code it mentions, tested where
  that code is plain Scala. `Node.assumption(statement)(formula)`: trusted, decided by the developer: the world
  outside the code (`stored.onlyCodeChanges`, `stored.initially(s => …)`, `stored.atomic`, a clock's `schedule`), an
  outside system's promise (an assumed operation's runs), what values from outside meet (`always[T]`).
  `Node.design(statement)(files*)`: a decision about code no proof covers.
- **Values.** `Declaration[A](means)`: abstract, known only through the statements about it; no code, define or
  program uses it. `Definition[A](means)`: what code and programs use, of any type; it must get a meaning, once:
  `implementProven(d)(code)` (a `program` or a `define`, proven), `implementTested(d)(env => …)` (plain Scala,
  tested), an operation's `StateModel` with `implementTested(ops*)(start, observe)(calls)` (proven on the model, the
  Scala tested against it), `op.assumed` (known by its assumptions), `implementValue(d)(v)`,
  `implementProvided(d*)`. `define { … }` and `program { … }` are Definitions given their meaning on the spot.
  `stated { … }` is a define whose body may apply a Declaration: name a line over Declarations with it, so a
  statement reads `viewFollows && editFollows`; only statements call it (code calling it does not compile).
- **Quantifiers.** `forall(x => …)`: every possible value. `exists(x => …)`: some value (Lean's `∃`; write it
  rather than `!forall(x => !…)`). `always[T](x => …)`: every value of `T` that can be made:
  a hypothesis in Lean of every statement about such values, met wherever covered code makes one (`made_`), and the
  tests draw only values meeting it. `always(stored)(s => …)`: every state the model reaches, kept by every program
  writing it (`cover_`), from a start that meets it (`start_`). An `always` is a node's whole formula; a claim of
  one placed with `.refines` is a rule below the statement it serves, no part of its step.
- **The World.** A statement holds in every reachable world and never names it. Read what changes in the current
  one: `stored.current`, a Declaration, a define reading state. A program in a statement runs from it:
  `book(request).result`, and `stored.in(book(request).after)` the state it leaves; beside a run, name the world
  before it with `.current` (`accepted(request).current`). Of a program that `.failsWith[E]`,
  `p(x).ifSucceeds(r => …)` and `p(x).ifFails(e => …)` say what each outcome does (each its `result.fold` with
  `True` on the other side): `handle(r).ifFails(_ => handle(r).changesNothing)`. `t.isConstant`: no run changes `t` (of a Declaration, an
  assumption). Two runs in sequence, and "eventually", cannot be stated.
- **A claim constrains every Definition and Declaration it mentions.** One applying a Definition to exactly its
  leading `forall` variables is a claim about its calls: the code given the Definition is checked against it, and
  code calling it is proven from it. When a claim holds only of some inputs (a room's bookings never overlap), give
  them a domain type whose `always` says so, rather than a precondition.
- **Edges.** `.refines(parent)`: a part (or a rule). `.assuming(assumption)`: a premise; FrFlow derives which a
  check rests on and refuses a list missing one or naming one not needed.
- **Examples are tests**, not nodes: `class GrantedExamples extends FrFlowExamples(Rooms.model):` then
  `example("back to back: granted"):` with a closed fact (`granted(…) is true`). `check` evaluates each against the
  code and, in Lean, against the claims. Nothing rests on them.
- **Consistency gates the proof.** Lean must prove that some meaning of every open value makes the statements at the
  bottom hold, group by group; a group not proven makes the model red. Give an open value an equation or a bound a
  witness comes from, or prove `consistent_<i>` by hand.

## Where things go

Each file is one concept: a type or a service, with its contract in its companion, the way Scala code is laid out
(rooms, auth in `examples/`). No top-level `val` or `def`.

- **The purpose** is an object named after the system (`object Rooms`, `object Auth`): its Declarations, its roots,
  and `lazy val model: FrModel`, which lists every node and composes the parts
  (`.pipe(Book.implemented).pipe(Calendar.implemented)…`). It names no code below it.
- **A domain type** is a case class; its companion holds the words it is spoken of in (`define`s), the assumptions of
  `always` on it, and its generators, added by `def generated(model: FrModel): FrModel`.
- **A service** is its Scala (a class) and, in its companion, its contract: its Definitions, its model, the claims and
  assumptions about them, and `def implemented(model: FrModel): FrModel` attaching its own code
  (`implementTested`, `implementProven`, `implementProvided`). A proven program is a `lazy val` there when it calls a
  part whose claims refine this service's.
- **Production wiring** is an object of its own with the design node that governs it (auth's `Server`).
- **Initialisation follows the DAG**: an object names its parents' objects, never its parts'. Only a `lazy val` (the
  FrModel, a program) may name what is below it.

## Writing nodes

From rooms (`examples/rooms`):

```scala
val booked = Declaration[List[Booking]]("the bookings made, as the world stands")
val accepted = Declaration[Booking => Boolean]("whether a request is accepted")
val book = Definition[Booking => Flow[Boolean]]("booking a request: whether it was booked")

val bookingsEndAfterStart = Node.assumption("Every booking ends after it starts.")(
  always[Booking](b => b.start < b.end))

val acceptWhenFree = Node.claim("A request is accepted exactly when its room is free for its whole time.")(
  forall((request: Term[Booking]) => accepted(request) === free(booked, request)))
  .assuming(bookingsEndAfterStart)

val acceptedIsAnswered = Node.claim("A request is accepted exactly when booking it answers booked.")(
  forall((request: Term[Booking]) => accepted(request).current === book(request).result))
  .refines(acceptWhenFree)

val neverOverlap = Node.claim("The bookings stored never overlap.")(
  always(storedBookings)(stored => stored.pairwise(apart)))
  .refines(bookWhenFree, acceptWhenFree)
  .assuming(nothingElseWrites, oneAtATime, startsEmpty, bookingsEndAfterStart)
```

And from the others:

```scala
val inMemorySessions = Node.design("One process decides every request, from the sessions and grants it holds " +
  "in memory.")("src/main/scala/auth/Server.scala")                                       // auth
val loadedKept = Node.claim("The accounts as loaded at start never change.")(seed.isConstant)  // keycloak
val searchKeeps = Node.assumption("A search changes nothing the database holds.")(           // crm
  forall((user: Term[Account], query: Term[Search]) =>
    databaseModel.in(fetch(user, query).after) === databaseModel.current))
```

- **Order.** Declare a `val` before its use (one used before it is defined is `null`): parents first.
- **Roots** have no `.refines`. An assumption is never a root, and never a part.
- **Designs** name the files they govern, relative to the project.

## Writing terms

Formulas and proven code are terms (`Term[A]`), built from the library's operations; what it does not offer is a type
error.

- **Annotate lambda parameters** as terms: `(b: Term[Booking], t: Term[BigInt]) => ...`; quantifiers too.
- **`===` and `=!=`**, never `==` (between terms it does not compile). `&&`, `||`, `!`, `implies`.
- **Records**: a field reads as on values (`b.start`); `make[RoomBookings](room, bookings)` builds one from terms;
  `b.updated(_.end, e)` copies with one field changed.
- **Matches** on an enum are `.on[Case](fields => ...)` per case; a case without fields is `.on[Case.type](...)`.
- **Conditionals**: `when(c)(a).otherwise(b)` (a term has no truth value while the formula is built);
  `let(v)(x => ...)` names a shared value; `some(x)`, `none[A]`.
- Operations on lists (`forall`, `exists`, `filter`, `map`, `foldLeft`, `contains`, `isEmpty`, `length`, `::`, `++`,
  `:+`, `pairwise`, `allDistinct`), options (`fold`, `getOrElse`, `isDefined`, `forall`, `exists`, and as their
  folds `map`, `filter`, `filterNot`, `contains`, `isEmpty`, `toList`), maps (`get`,
  `getOrElse`, `updated`), sets (`contains`, `union`), and `BigInt` arithmetic and comparisons. Maps and sets are
  not iterated.
- **In plain Scala** (implementations, wiring, tests): `d.fn(env)` runs a define, `env(d)` reads a Definition's value.

## Programs and models

Use a program when code takes several steps against a state (load, store, log): its order, its loop and its
transaction are then proven, not only reviewed.

```scala
val inRoom = Definition[String => Flow[RoomBookings]]("a room's bookings, as the SQLite table gives them")
val add = Definition[Booking => Flow[Unit]]("a booking added to the SQLite table")

object storedBookings extends StateModel[List[Booking]]("every booking stored, oldest first"):
  inRoom.means(room => state.get.map(stored => make[RoomBookings](room, stored.filter(b => b.room === room))))
  add.means(booking => state.update(stored => stored :+ booking))

val bookIfGranted = program { (request: Term[Booking]) =>
  (for
    held  <- inRoom(request.room)
    booked = granted(held, request)
    _     <- Flow.when(booked)(add(request))
  yield booked).atomically }
```

- **A model** says what each operation does to its state (`state.get`, `state.set`, `state.update`). Its Scala is
  attached with `implementTested(ops*)(start = …, observe = …)(t => (t.op1, t.op2))` and tested against it on
  generated runs, two calls at once among them. Say of the model, as assumptions, what the world does: nothing else
  changes it (`onlyCodeChanges`), what it starts in (`initially`), runs never interleave (`atomic`). Which programs
  change it FrFlow derives from the code.
- **An outside system known only by its promises**: `op.assumed` in its model, its promises assumptions about its
  runs (`op(x).result`, `model.in(op(x).after)`). It reads only its own model; what it needs of another is handed to
  it as an input. Its results are values from outside.
- **Failures**: a model whose calls may fail is `StateModel.failing[S, E](means, error)`; a program that can fail is
  declared `Definition[…]("…").failsWith[E]`, and its `.result` is an `Either[E, R]`. FrFlow checks the declaration
  against the code.
- **Combinators**: `Flow.when`, `cond`, `ifM`, `each`, `collect`, `fold`, `parCollect(N)`, `(a, b).parTupled`,
  `race`, `raise`, `handle`, `attempt`, `guarantee`, `bracket`, `timeout(Clock.now, s)`, `retry(Clock.sleep, waits)`.
  Steps at once are proven to commute where they touch a model in common (`commute_<i>`); a side that may let an
  error out beside one that may fail or writes is refused.
- **Time** is Cats Effect's: `Clock.now`, `Clock.sleep(d)`; the world moves the time between runs (`elapse`) and at
  each of the clock's steps, so a program may not rely on taking no time. A schedule
  (`Clock.clockModel.schedule(other)((now, o) => …)`) is a trusted fact restricting the world's steps.
- **Production** runs programs with `model.running[IO](model := impl, …)` and plain code with
  `model.code(d)(bindings*)`; nothing checks a call there. Wire it in a file a design node governs.

## Terms or plain Scala

Write terms where the code is small and worth proving (a decision rule, a program's steps); write plain Scala for the
lowest-level code (a lookup through an index, a parser, SQL), and attach it with `implementTested`:

```scala
.implementTested(granted)(_ => (held, request) => Calendar(held).grants(request))                  // rooms
.implementTested(inRoom, add)(start = BookingsTable.holding, observe = _.bookings)(t => (t.inRoom, t.add))
```

The test's property is the claim's own formula; its cases are drawn from the generators given for the types
(`.withGenerator(gen.describedAs("…"))`), each meeting the rules on its type, seeded with the examples. Never write a
property by hand, and never weaken a claim or an example to make a test pass.

- **A failing case** names the inputs, the seed, the case and its size: reproduce it as an example, fix the code, and
  run `check` again.
- **A generator** for a type says what values can occur (a table: one row per key); say in its description what it
  leaves out. `check` notes a generator that never makes the examples' values.
- **A model's Scala failing its model** reads as the calls, the state and what each gave: fix the Scala, or tell the
  developer the model is wrong; never change the model to match the code without their decision.

## What check reports, and what to do

A try is `shown` (Lean proved it) or `not shown`. Never write that Lean shows a part needed unless it does.

| Report | Means | Do |
|---|---|---|
| `complete` open | the parts may not make it | Usually a part is missing or too weak. If they do make it, prove it by hand. |
| a step is refuted on … | Lean confirms a case where the parts hold and the node does not | A part is wrong or missing. |
| `needed_C` shown | the node holds without C | C belongs elsewhere, or another part says too much. |
| `vacuous`, `restates` shown | the node says nothing, or what its part says | Strengthen it, merge it, or say what it adds. |
| `clash`, `unsat` shown | the parts contradict each other; nothing meets the node | Fix the parts, or the node. |
| `idle` shown | doing nothing meets the roots | State what users can do. |
| `impl` open | the code does not provably meet the claim | Fix the code, or prove `impl` by hand. |
| `cover_`, `made_`, `start_` open; "keeping R is not proven" | a rule is not kept, made or started | Fix the code, the start, or the rule; a statement taking an open rule stays open. |
| consistency not proven | no meaning is shown for a group | Add an equation or bound a witness comes from, or prove `consistent_<i>` by hand. |
| fails a generated case | tested code does not meet its claim | Add the case as an example; fix the code. |
| trusted, not tested | an assumption no generated run can evaluate | Write it as a run of one operation with a Scala value, or tell the developer it is trusted. |
| `PremiseMissing`, `PremiseNotNeeded` | the `.assuming` list differs from what the check rests on | List what it names, or drop what it does not. |
| an example fails (`x`: the code does not hold it, or the claims contradict it) | the code or the claim is wrong | Fix the code or the claim before any proof; never the example to make it pass. |
| an example not decided by the claims (`o`) | Lean's automation did not decide it within its budget | Nothing to fix: leave the example as it is; prove `example_<set>_<i>` in `Whole.lean` only if the developer asks. |
| Lean and Scala disagree | an example gives one result in Lean and another in Scala | FrFlow's printer or evaluator is wrong: report it; never change the example. |

## Proving by hand

1. `scaffold NODE` writes `lean/Proofs/<Model>/<node>.lean` (its `Spec` imported, in namespace
   `<Model>.<node>.Proofs`): per obligation the last check left open, `theorem <name> : Obl.<name> := by sorry`,
   whose proof you write (`unfold Obl.<name>` first; `check` prints the goal Lean is left with).
2. Iterate with `lake env lean Proofs/<Model>/<node>.lean` in `lean/`, then `check`. `simp only [frflow_defs]`
   unfolds the model's definitions and a program's run on the models.
3. Shared lemmas go in `lean/Proofs/<Model>/Lemmas.lean`, which imports no lemmas of its own. Lean 4.35 deprecates
   `if_pos`/`if_neg`: use `ite_eq_left`/`ite_eq_right`, or `split`.
4. A proof file holds only `import`, `set_option` (`maxHeartbeats`, `maxRecDepth`, `autoImplicit`, `linter.*`),
   `open`, `namespace`, `section`, `noncomputable` and theorems with tactic proofs (no `sorry`, `axiom`, `admit`,
   attributes or metaprograms), and imports only `FrFlowGen.<Model>.Domain`, `FrFlowGen.<Model>.<node>.Spec`,
   `FrFlowGen.<Model>.Whole.Spec`, `FrFlow`, `Std`, `Init`, `Proofs.<Model>.Lemmas`. Only `propext`,
   `Classical.choice` and `Quot.sound` may be among a proof's axioms.
5. Never prove a step from a contradiction in the parts, or without them.
6. A consistency group FrFlow cannot witness is proven by `theorem consistent_<i>` in
   `lean/Proofs/<Model>/Whole.lean` (importing `FrFlowGen.<Model>.Whole.Spec`), with a witness that shows what is
   assumed can be done.
