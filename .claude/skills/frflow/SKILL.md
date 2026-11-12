---
name: frflow
description: >-
  Develop a system with FrFlow: a small set of root statements (the idea's purpose, kept concise) refined by a DAG
  of small statements in the domain's words, each proven in Lean from its parts and decided by the developer. Use
  when turning an idea into roots, proposing or changing nodes, introducing domain types and values, adding
  examples, answering the developer's requests, proving a step, or giving code its meaning; or when the work touches
  `Node.claim`, `Node.assumption`, `Node.design`, `Declaration`, `Definition`, `define`, `stated`, `lifted`,
  `FrSpec`, `contractOf`, `forall`, `exists`, `always`, `FrModel`, `FrFlowExamples`, `.refines`, `.assuming`,
  `.replaces`, `.define`, `.defineTested`, `.defineValue`, `.provided`, `.defining`, `withGenerator`, `.holding`,
  `.current`, `.in`, `.after`, `.result`, `.steps` or `.amongOthers`.
---

# Developing with FrFlow

The developer tells you the idea in chat; you ask what you need, record the conversation, and draft the project's
README from it. Then you write Scala nodes: a small set of roots, kept concise (one idea each), and below them parts
that together prove them, down to claims about the code. Lean proves each step; the developer decides every node. The
README explains the method, `docs/USAGE.md` is the reference, `docs/DAG.md` the design.

These rules are the agent layer's (`frflow.agent`), on top of FrFlow's core. A project uses it when its main object
names it, `FrFlowApp(frModel, root = "examples/NAME", extensions = List(frflow.agent.Agent))`; without it, `said`,
`asked`, `replied`, `conversation`, `ask`, `close`, `context` and `answer` are not there, and `inbox` lists no
requests. Do not add it to a project whose developer set it up without the layer.

## Starting a project: the conversation

1. **Set up.** The developer runs `sbt "frflowInitAgent NAME --as THEIR_NAME"` (a lowercase name; `--as` signs the
   deciders' list with their key, so it is theirs to run), then `sbt reload`: an empty FrModel in `examples/NAME`,
   with the agent layer. `bin/frflow NAME status` works from here.
2. **Let the developer tell the idea**, in their own words, as long or short as they like. Record it verbatim:
   `said TEXT` (each message that tells the idea or corrects it). Do not write files yet.
3. **Ask, 3 to 5 questions at a time**, each with the answer you assume, so the developer can agree or correct it:
   "Can a company share a record with another? I assume yes, only the owner can, until a date." Ask what decides the
   roots and the first split: who the users are, what they can do, what must never happen, what the system keeps,
   what comes from outside and what is trusted of it, what is out of scope. Record each before asking it:
   `asked QUESTION --assume ANSWER`; record each answer as said: `replied QUESTION TEXT`. Stop when the roots can be
   stated; ask later questions when a node needs them, the same way.
4. **Restate the purpose in a sentence or two** ("A user finds exactly …") and ask the developer to confirm or
   correct it in chat. It becomes the roots.
5. **Draft the README** from the conversation, in the developer's words where possible: what the system is for, what
   users do, what must never happen, and what is not modelled. It is ordinary documentation: FrFlow does not read
   it, no node refers to it, and nothing in it refers to the conversation's questions.
6. **Then propose the roots and the first parts.** Where a node needs something the developer has not said, ask
   (step 3) instead of guessing. The reason a node holds is the developer's, given when they decide it: put your
   rationale in your `answer`, not in the node.

`conversation` shows what is recorded.

## Rules

1. **You propose; the developer decides.** Never edit `.frflow/ledger.json` or `.frflow/deciders`, decide for the
   developer, create or look for a signing key, or run `deciders`, `accept`, `confirm` or `rebase` for them. Record
   the conversation only as it happened: never a reply the developer did not give. If `status` says a decision does
   not count, tell the developer.
2. **One statement per node**, one sentence in the developer's domain words; the formula says exactly that sentence.
   No concepts glued with `&&`: two ideas are two nodes, and what always holds is an `always` of its own.
3. **A part is never a restatement.** Say what the domain adds (a concept, a mechanism, a rule), or state the claim
   about the code at the parent directly.
4. **2 to 5 parts per parent, as a rule.** More asks for an intermediate node.
5. **The roots are stated as exactly**: what users can do and what must never happen, as one relation (`===`,
   "exactly when"), so that a system doing nothing does not meet them. Where the purpose is more general than the
   code, state it over `Declaration`s, and say at the bottom what each is in terms of the code (rooms'
   `bookedAfterIsStored`).
6. **The first split is ⇒/⇐** (safety and capability) **or state/reads**, not one part per conjunct.
7. **Introduce the domain as it is needed**: a domain type (a case class or an enum deriving `LeanType`) where the
   idea needs one, a `Declaration` for each word of the model: a concept known only by what is said of it, or one
   code provides, which then gets a Definition. Every Declaration says what it means, and every Definition where
   its value comes from.
8. **What comes from outside has a type of its own**, and what is trusted of it is an assumption of `always` on that
   type. Never state an assumption about a function's inputs.
9. **Offer real alternatives**: the second `.replaces` the first; say the trade-off in your `answer`.
10. **Never weaken a node to make a proof or a test go through.** A false step means a part is wrong or missing; a
    failing generated case means the code is wrong, or the claim as decided is. If the idea or a decided node is
    wrong, say so.
11. **Never edit generated Lean** (`lean/FrFlowGen/`). Lean you write goes only in `lean/Proofs/<Model>/`.
12. **Every source file is governed by one node**: the claim whose code it is, or a design node (production wiring,
    the call to `knowledge.code` or `knowledge.running`, goes in one).
13. **Say what is not modelled** (in the README, and in your `answer`), and name the waiting nodes that are
    mechanical.
14. **Names.** A node's id is its `val`'s name, as are a Declaration's and a Definition's; ids are unique and
    distinct from every type and value. A `val` named after a Lean word (`decide`, `max`, `id`, `holds`) is refused;
    one named after a facade name (`after`, `result`, `when`, `always`) hides it. To rename a node, change its val
    and move its proof file; `.replaces(old)` links the two.
15. **Changes.** A change of meaning reviews what rests on the node; a change to governed code reviews the node:
    say why what rests on it still holds.

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

`ci` is `check`, then `status`. Exit codes: 0 fine; 1 not complete, or refused; 2 a usage error; 3 no Lean.

## The core concepts

Three kinds of nodes, two kinds of values, two quantifiers (the owner's decisions §15). There is nothing else: no
contract, invariant, model or definition node, no boundary, no program type, no state model. Never work around
them.

- **Nodes.** `Node.claim(statement)(formula)`: proven from its parts or of the proven code it mentions, tested where
  that code is plain Scala. `Node.assumption(statement)(formula)`: trusted, decided by the developer: an outside
  system's promise, what values from outside meet (`always[T]`).
  `Node.design(statement)(files*)`: a decision about code no proof covers.
- **Values.** `Declaration[A](means)`: a word of the model, of any type, what statements speak of and code calls.
  A Definition is a Declaration with a meaning; list it in the `FrModel` beside the nodes
  (`FrModel("Rooms")(bookWhenFree, …, bookings.define(lifted[StoredBookings]))`). A word gets one, once:
  `d.define(code)` or `d.define { (a, b) => … }` (a `define`, lifted code, a class read for a structure: proven),
  `d.defineTested(env => …)` (plain Scala, tested), `d.defineValue(v)`, `d.provided`. `define { … }` is a Definition
  declared and defined at once, named as its val; it needs no listing. A word the model gives no meaning is known
  by the statements about it: if code calls it, it is a function from outside (say what is assumed of it).
  Type what calls a word by `Declaration`; never write `Definition[A]("…")` or `implement…`, which no longer
  exist. Read a field of a declared record as `d.term.field`.
  `stated { … }` is a define whose body may apply a Declaration: name a line over Declarations with it, so a
  statement reads `viewFollows && editFollows`; only statements call it (code calling it does not compile).
- **Quantifiers.** `forall(x => …)`: every possible value. `exists(x => …)`: some value (Lean's `∃`; write it
  rather than `!forall(x => !…)`). `always[T](x => …)`: every value of `T` that can be made:
  a hypothesis in Lean of every statement about such values, met wherever covered code makes one (`made_`), and the
  tests draw only values meeting it. An `always` is a node's whole formula; a claim of
  one placed with `.refines` is a rule below the statement it serves, no part of its step.
- **Structures.** A value with members (a service, a store) is a trait of the developer's and a
  `Declaration[Trait]("…")` typed by its members: `bookings.book(request).result` is what a call gives,
  `bookings.booked.in(bookings.book(request).after)` a member read after it, `bookings.current` the structure as it
  stands. A claim on a structure holds of it in every state, so state an invariant as what each call keeps. Its
  Definition is the class that implements the trait, `bookings.define(lifted[StoredBookings])`, compiled from its
  TASTy and proven. "Eventually" cannot be stated.
- **A claim constrains every Definition and Declaration it mentions.** One applying a Definition to exactly its
  leading `forall` variables is a claim about its calls: the code given the Definition is checked against it, and
  code calling it is proven from it. When a claim holds only of some inputs (a room's bookings never overlap), give
  them a domain type whose `always` says so, rather than a precondition.
- **Edges.** `.refines(parent)`: a part (or a rule). `.assuming(assumption)`: a premise; FrFlow derives which a
  check rests on and refuses a list missing one or naming one not needed.
- **Examples are tests**, not nodes: `class GrantedExamples extends FrFlowExamples(rooms):` then
  `example("back to back: granted"):` with a closed fact (`granted(…) is true`). `check` evaluates each against the
  code and, in Lean, against the claims. Nothing rests on them.
- **Consistency gates the proof.** Lean must prove that some meaning of every open value makes the statements at the
  bottom hold, group by group; a group not proven makes the model red. Give an open value an equation or a bound a
  witness comes from, or prove `consistent_<i>` by hand.

## Writing nodes

From rooms (`examples/rooms`):

```scala
trait Bookings extends Mutable:
  update def book(request: Booking): Boolean
  def booked: List[Booking]

val bookings = Declaration[Bookings]("the bookings of the meeting rooms")

val acceptWhenFree = Node.claim("A request is accepted exactly when its room is free for its whole time.")(
  forall((request: Term[Booking]) =>
    wellFormed(bookings.booked, request) implies
      (bookings.book(request).result === free(bookings.booked, request))))

val neverOverlap = Node.claim("Booking a request leaves bookings that do not overlap not overlapping.")(
  forall((request: Term[Booking]) =>
    (wellFormed(bookings.booked, request) && bookings.booked.pairwise(apart)) implies
      bookings.booked.in(bookings.book(request).after).pairwise(apart)))

val answerWhenNoOverlap = Node.claim("A request is answered booked exactly when it overlaps no booking.")(
  forall((request: Term[Booking]) =>
    bookings.book(request).result === bookings.booked.forall(b => noOverlap(b, request))))

val rooms: FrModel = FrModel("Rooms")(acceptWhenFree, neverOverlap,
  answerWhenNoOverlap.refines(acceptWhenFree), bookings.define(lifted[StoredBookings]))
```

And from the others:

```scala
val inMemorySessions = Node.design("One process decides every request, from the sessions and grants it holds " +
  "in memory.")("src/main/scala/auth/Server.scala")                                       // auth
val bookingsEndAfterStart = Node.assumption("Every booking ends after it starts.")(
  always[Booking](b => b.start < b.end))
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
- **In plain Scala** (implementations, wiring, tests): `d.fn(env)` runs a define, `env(d)` reads a word's value.

## Services with state

A service with state is a structure: write its interface as a trait (a `caps.Mutable` when a member changes it),
its claims on the `Declaration` of that trait, and its code as a class that implements it; `lifted[Class]` reads the
class. `examples/rooms` is the smallest one, `examples/payments` one made of several structures.

- **An outside system known only by its promises** is a structure given no class (`pricing.provided`), its promises
  assumptions on its members.
- **Production** calls the classes themselves, and plain code with `knowledge.code(d)(bindings*)`; nothing checks a
  call there. Wire it in a file a design node governs.

## Terms or plain Scala

Write terms where the code is small and worth proving (a decision rule); write plain Scala for the
lowest-level code (a lookup through an index, a parser, SQL), and give it with `defineTested`.

A decision rule can also be proven as the Scala it is: `val noOverlap = lifted { (a: Booking, b: Booking) => … }` is
a Definition given its meaning on the spot, read at compile time from an ordinary function of one to four inputs
(`docs/LIFTED.md`). Use it for a function with no state, no effect and no failing call, over `BigInt`, `Boolean`,
`String`, case classes, enums, lists, options, maps and sets, calling other lifted functions and `inline def`s
(ordinary methods too where the project compiles with `-Yretain-trees`); a Declaration is defined by it with
`d.define(code)`. A
compile error names the Scala it does not read (a `var`, `Int` arithmetic, `head`, a value from outside, recursion):
rewrite that part, or keep the function as tested plain Scala. Every type in it has an `FrSpec`
(`derives FrSpec`, or `given FrSpec[T] = FrSpec.derived[T].where(v => …)` with its contract; an id is never a
bare `String`: `opaque type PaymentId = String` with `object PaymentId extends FrSpec.Opaque[PaymentId, String]`,
both at the top level of one file, which Lean reads as the string it is over); the contract enters
the model only when a node states it (`Node.assumption("…")(contractOf[T])`, the developer's to decide). Statements
stay in the DSL.

A service can be proven as written. Write it as a structure, a value with members (`examples/payments`,
`docs/LIFTED.md` "A structure: a value with members"): a trait of its members; when a member changes it, the trait
extends `caps.Mutable`, with what changes it marked `update`, in a file with capture and separation checking; when
none does, a plain trait that is not sealed, its members over domain types; in the trait's companion `val limits = Declaration[CardLimits]("…")` and the claims,
through the members (`limits.authorise(p).result`, `.after`, `limits.decided(id).in(state)`, `limits.current`); a
class that implements the trait; and in the model its Definition, `limits.define(lifted[RecordedLimits])`, which
compiles the class from its TASTy when the model is built (Scala it does not read is a `NotRead` then, with the
file and line; the project names `scala3-tasty-inspector` as a dependency). A class
made of structures is given their words (`lifted[StreamPaymentHandler](limits, ledger, offsets)`) and is proven
from the claims on them, so wire those claims under its own with `.refines`; in a member that changes the class,
give each call of a held structure a statement of its own. Never add a member to a trait for a claim's sake: say
what the holder does through the interfaces of what it holds, asked as it has them
(`ledger.posted(p.id).in(handler.handle(p).after)`; `ledger.total` beside `handler.handle(p)` is the held
ledger's), and write shared vocabulary ("a payment is applied") as a definition in the model. A claim holds of the structure in every state: state an invariant as what each call keeps. For a crash and for other callers, claim over the call's steps
(`call.steps`, `call.amongOthers(run => run.steps.forall(step => …))`, `run.others` for what it takes of them),
and claim that each of its own steps grants what it takes. Name a state's type `limits.State`, never
`Term[CardLimits]`. In an example give a state with `limits.holding(RecordedLimits(…))`. Give one class per trait in a
model.

The earlier way, a word per method, is still read (`examples/shop`,
`docs/LIFTED.md` "Services"): the store is a `caps.Mutable` class with one `var`, the service a class holding it
(`Ledger^`), in files with capture and separation checking. A service holding several stores or services names
its state in its companion (`type State = …`, a case class with a field per port, in order); give every port's
methods names of their own, each of one argument, so a call of one is read as a call of its word. Put the contracts in the
companions: a `Declaration` per method, the method read with
`updating { (port: S^, input: A) => port.method(input) }` and listed as its Definition
(`Ledger.claim.define(Ledger.claimCode)`), and claims over the word. For races, read it with `interleaving { … }(others)` and claim over every schedule;
state what the reading takes for granted as design nodes (each store method is one transaction; other calls keep
the rely), and prove the service's own steps keep the rely for others. Bind a value whose type has a contract last
in a `forall`. In the hand proofs, take a method read among other calls apart with `extract_lets` and share one
lemma over its steps (`every_step` in the examples); a proof file holds theorems only, no `def`.

Plain Scala given with `defineTested`, each listed in the model:

```scala
admit.defineTested(env => SessionStore(env(grants), env(sessions)).decide)                           // auth
```

The test's property is the claim's own formula; its cases are drawn from the generators given for the types
(`.withGenerator(gen.describedAs("…"))`), each meeting the rules on its type, seeded with the examples. Never write a
property by hand, and never weaken a claim or an example to make a test pass.

- **A failing case** names the inputs, the seed, the case and its size: reproduce it as an example, fix the code, and
  run `check` again.
- **A generator** for a type says what values can occur (a table: one row per key); say in its description what it
  leaves out. `check` notes a generator that never makes the examples' values.

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
| `made_` open; "keeping R is not proven" | a rule is not met by what the code makes | Fix the code or the rule; a statement taking an open rule stays open. |
| consistency not proven | no meaning is shown for a group | Add an equation or bound a witness comes from, or prove `consistent_<i>` by hand. |
| fails a generated case | tested code does not meet its claim | Add the case as an example; fix the code. |
| `PremiseMissing`, `PremiseNotNeeded` | the `.assuming` list differs from what the check rests on | List what it names, or drop what it does not. |
| an example fails (`x`: the code does not hold it, or the claims contradict it) | the code or the claim is wrong | Fix the code or the claim before any proof; never the example to make it pass. |
| an example not decided by the claims (`o`) | Lean's automation did not decide it within its budget | Nothing to fix: leave the example as it is; prove `example_<set>_<i>` in `Whole.lean` only if the developer asks. |
| Lean and Scala disagree | an example gives one result in Lean and another in Scala | FrFlow's printer or evaluator is wrong: report it; never change the example. |

## Proving by hand

1. `scaffold NODE` writes `lean/Proofs/<Model>/<node>.lean` (its `Spec` imported, in namespace
   `<Model>.<node>.Proofs`): per obligation the last check left open, `theorem <name> : Obl.<name> := by sorry`,
   whose proof you write (`unfold Obl.<name>` first; `check` prints the goal Lean is left with).
2. Iterate with `lake env lean Proofs/<Model>/<node>.lean` in `lean/`, then `check`. `simp only [frflow_defs]`
   unfolds the model's definitions.
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
