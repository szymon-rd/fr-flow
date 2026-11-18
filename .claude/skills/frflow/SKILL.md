---
name: frflow
description: >-
  Run as /frflow to start a new system from an idea (the agent sets everything up), or to continue one. Develop a
  system with FrFlow: a small set of root statements (the idea's purpose, kept concise) refined by a DAG
  of small statements in the domain's words, each proven in Rocq from its parts and decided by the developer. Use
  when turning an idea into roots, proposing or changing nodes, introducing domain types and values, adding
  examples, answering the developer's requests, proving a step, or giving code its meaning; or when the work touches
  `Node.claim`, `Node.assumption`, `Node.design`, `Declaration`, `Definition`, `define`, `stated`, `lifted`,
  `FrSpec`, `contractOf`, `forall`, `exists`, `always`, `FrModel`, `FrFlowExamples`, `.refines`, `.assuming`,
  `.replaces`, `.define`, `.defineTested`, `.defineValue`, `.provided`, `.defining`, `withGenerator`, `.holding`,
  `.current`, `.in`, `.after`, `.result`, `.following`, `.again`, `.andThen`, `.changesNothing`, `.unchangedBy`,
  `.isIdempotent`, `.steps` or `.amongOthers`.
---

# Developing with FrFlow

The developer tells you the idea in chat; you ask what you need, record the conversation, and draft the project's
README from it. Then you write Scala nodes: a small set of roots, kept concise (one idea each), and below them parts
that together prove them, down to claims about the code. Rocq proves each step; the developer decides every node. The
README explains the method, `docs/USAGE.md` is the reference, `docs/DAG.md` the design.

These rules are the agent layer's (`frflow.agent`), on top of FrFlow's core. A project uses it when its main object
names it, `FrFlowApp(frModel, root = "examples/NAME", extensions = List(frflow.agent.Agent))`; without it, `said`,
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
   `Declaration` and the node saying what it is in the code only where the purpose is more general than the code.
6. **Below the promises comes the rule**: each operation's one specification, split at most into what it does and
   what it refuses; then the design decisions; then the code.
7. **Introduce the domain as it is needed**: a domain type (a case class or an enum deriving `RocqType`) where the
   idea needs one, a `Declaration` for each word of the model: a concept known only by what is said of it, or one
   code provides, which then gets a Definition. Every Declaration says what it means, and every Definition where
   its value comes from.
8. **What comes from outside has a type of its own**, and what is trusted of it is an assumption of `always` on that
   type. Never state an assumption about a function's inputs.
9. **Offer real alternatives**: the second `.replaces` the first; say the trade-off in your `answer`.
10. **Never weaken a node to make a proof or a test go through.** A false step means a part is wrong or missing; a
    failing generated case means the code is wrong, or the claim as decided is. If the idea or a decided node is
    wrong, say so.
11. **Never edit generated Rocq** (`rocq/FrFlowGen/`). Rocq you write goes only in `rocq/Proofs/<Model>/`.
12. **Every source file is governed by one node**: the claim whose code it is, or a design node (production wiring,
    the call to `knowledge.code` or `knowledge.running`, goes in one).
13. **Say what is not modelled** (in the README, and in your `answer`), and name the waiting nodes that are
    mechanical.
14. **Names.** A node's id is its `val`'s name, as are a Declaration's and a Definition's; ids are unique and
    distinct from every type and value. A `val` named after a word the generated files use (`decide`, `max`, `id`, `holds`) is refused;
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
  a lemma of the proof (`rocq/Proofs/<Model>/Lemmas.v`), never a node: there is nothing in it to decide.
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
   every node you propose is proven (by FrFlow's automation or by your proof in `rocq/Proofs/<Model>/`) or tested
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
| `stands [NODE]` | What the node, or each root, stands on at the bottom: its assumptions, and the claims not proven. |
| `render` | Rebuild from the Scala; elaboration errors and the model's problems come back here. |
| `check [NODE]` | Prove what changed, test the code, evaluate the examples. Slow. A `timeout` is not a failure: run it again. |
| `status` | The tree, the summary and the warnings; exits 1 unless the FrModel is complete. |
| `scaffold NODE` | Stubs in the node's proof file for what the last check left open. |
| `answer REQUEST\|NODE TEXT` | Reply to a request, or tell the developer of work they did not ask for. |
| `wait [--minutes N]` | Block until the developer decides or asks; print what moved. Run it in the background. |

`ci` is `check`, then `status`. Exit codes: 0 fine; 1 not complete, or refused; 2 a usage error; 3 no Rocq.

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
- **Quantifiers.** `forall(x => …)`: every possible value. `exists(x => …)`: some value (Rocq's `exists`; write it
  rather than `!forall(x => !…)`). `always[T](x => …)`: every value of `T` that can be made:
  a hypothesis in Rocq of every statement about such values, met wherever covered code makes one (`made_`), and the
  tests draw only values meeting it. An `always` is a node's whole formula; a claim of
  one placed with `.refines` is a rule below the statement it serves, no part of its step.
- **Structures.** A value with members (a service, a store) is a trait of the developer's and a
  `Declaration[Trait]("…")` typed by its members: `bookings.book(request).result` is what a call gives,
  `bookings.booked.in(bookings.book(request).after)` a member read after it, `bookings.current` the structure as it
  stands. A claim on a structure holds of it in every state, so state an invariant as what each call keeps. Its
  Definition is the class that implements the trait, `bookings.define(lifted[StoredBookings])`, compiled from its
  TASTy and proven. "Eventually" cannot be stated. What calls say of each other has shorthands, each built of `.in`
  and `.after`: `q.following(c)` is `q.in(c.after)`, `c.again` is `c.in(c.after)`, `c.andThen(r => d(r))` is
  `d(c).in(c.after)`, `c.changesNothing` is `c.after` equal to the state `c` is made on, `q.unchangedBy(c)` is
  `q.following(c) === q`, and `c.isIdempotent` is `(c.again === c) && (c.again.after === c.after)`
  (`examples/links`).
- **A claim constrains every Definition and Declaration it mentions.** One applying a Definition to exactly its
  leading `forall` variables is a claim about its calls: the code given the Definition is checked against it, and
  code calling it is proven from it. When a claim holds only of some inputs (a room's bookings never overlap), give
  them a domain type whose `always` says so, rather than a precondition.
- **Edges.** `.refines(parent)`: a part (or a rule); `whole.from(parts*)` says the same where the whole is stated. `.assuming(assumption)`: a premise; FrFlow derives which a
  check rests on and refuses a list missing one or naming one not needed.
- **Examples are tests**, not nodes: `class LinksExamples extends FrFlowExamples(links):` then
  `example("a URL shortened again: its code"):` with a closed fact (`shortener.shorten(home).in(one).result is
  Code(0)`). `check` evaluates each against the
  code and, in Rocq, against the claims. Nothing rests on them.
- **Consistency gates the proof.** Rocq must prove that some meaning of every open value makes the statements at the
  bottom hold, group by group; a group not proven makes the model red. Give an open value an equation or a bound a
  witness comes from, or prove `consistent_<i>` by hand.

## Writing nodes

From the link shortener (`examples/links`):

```scala
trait Links extends Mutable:
  update def shorten(url: Url): Code
  def resolve(code: Code): Option[Url]
  update def remove(code: Code): Unit

val shortener = Declaration[Links]("the link shortener: the codes it has given and the URLs they lead to")

val shortenedCodeResolves = Node.claim("The code a URL is given leads to that URL.")(
  forall((u: Term[Url]) => shortener.shorten(u).andThen(code => shortener.resolve(code)) === some(u)))

val removeChangesOnlyThatCode = Node.claim("Once a code is removed, every code leads where it led before, but " +
    "the removed one, which leads nowhere.")(
  forall((c: Term[Code], d: Term[Code]) =>
    shortener.resolve(d).following(shortener.remove(c)) ===
      when(d === c)(none[Url]).otherwise(shortener.resolve(d))))

val removedCodeLeadsNowhere = Node.claim("A removed code leads nowhere.")(
  forall((c: Term[Code]) => shortener.resolve(c).following(shortener.remove(c)).isEmpty))

val links: FrModel = FrModel("Shortener")(shortenedCodeResolves, removeChangesOnlyThatCode,
  removedCodeLeadsNowhere.refines(removeChangesOnlyThatCode), /* … */ shortener.define(lifted[RetiringLinks]))
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
class. `examples/links` is one service; `examples/payments` one made of several structures.

- **An outside system known only by its promises** is a structure given no class (`pricing.provided`), its promises
  assumptions on its members.
- **Production** calls the classes themselves, and plain code with `knowledge.code(d)(bindings*)`; nothing checks a
  call there. Wire it in a file a design node governs.

## Terms or plain Scala

Write terms where the code is small and worth proving (a decision rule); write plain Scala for the
lowest-level code (a lookup through an index, a parser, SQL), and give it with `defineTested`.

Code that keeps state (a service) is proven as the Scala it is, written as a structure (below). Every type of a
value in it has an `FrSpec`: `derives FrSpec`, or `given FrSpec[T] = FrSpec.derived[T].where(v => …)` with its
contract, written with the DSL over a `Term[T]`. An id is never a bare `String`: `opaque type PaymentId = String`
with `object PaymentId extends FrSpec.Opaque[PaymentId, String]`, both at the top level of one file, which Rocq
reads as the string it is over. The contract enters the model only when a node states it
(`Node.assumption("…")(contractOf[T])`, the developer's to decide).

A service can be proven as written. Write it as a structure, a value with members (`examples/links`,
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
ledger's; a structure the held one holds in turn is reached the same way, and `ledger.in(state)` names a held
structure whole), and write shared vocabulary ("a payment is applied") as a definition in the model. A claim holds of the structure in every state: state an invariant as what each call keeps. For a crash and for other callers, claim over the call's steps
(`call.steps`, `call.amongOthers(run => run.steps.forall(step => …))`, `run.others` for what it takes of them),
and claim that each of its own steps grants what it takes. Name a state's type `limits.State`, never
`Term[CardLimits]`. In an example give a state with `limits.holding(RecordedLimits(…))`. Give one class per trait in a
model.

A class made of other structures is given their words where it is lifted
(`checkout.define(lifted[ShopCheckout](inventory, payments, orders))`), and its claims are said through what those
expose (`inventory.available(sku)`, as the checkout has it): a structure held two levels down is not read through
its holder's holder, so give the one between a member for what the claim needs. State what the
reading takes for granted as design nodes (each member of a store that changes it is one transaction). Bind a value
whose type has a contract last in a `forall`.

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

A try is `shown` (Rocq proved it) or `not shown`. Never write that Rocq shows a part needed unless it does.

| Report | Means | Do |
|---|---|---|
| `complete` open | the parts may not make it | Usually a part is missing or too weak. If they do make it, prove it by hand. |
| a step is refuted on … | Rocq confirms a case where the parts hold and the node does not | A part is wrong or missing. |
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
| an example not decided by the claims (`o`) | FrFlow's automation did not decide it within its budget | Nothing to fix: leave the example as it is; prove `example_<set>_<i>` in `Whole.v` only if the developer asks. |
| Rocq and Scala disagree | an example gives one result in Rocq and another in Scala | FrFlow's printer or evaluator is wrong: report it; never change the example. |

## Proving by hand

1. `scaffold NODE` writes `rocq/Proofs/<Model>/<node>.v` (its `Spec` imported): per obligation the last check left
   open, `Lemma <node>_Proofs_<name> : <node>_Obl_<name>.` with `Admitted`, whose proof you write in its place
   (`check` prints what Rocq said of it).
2. Iterate with `check NODE`: it compiles what changed and nothing else, and says of each lemma whether Rocq accepts
   it. To try a proof in an editor, open the file in `rocq/` (`rocq/_CoqProject`, which `check` writes, points at
   what it compiled). `autounfold with frflow_defs in *` unfolds the model's definitions; `frflow_auto` is what
   FrFlow tried; `frflow_simpl` rewrites the lists and takes each `if` by cases; `frflow_evaluate` runs the code on
   values written out, each step once. A condition FrFlow found no values for ("can hold: not shown") is proven in
   `rocq/Proofs/<Model>/Whole.v` by giving them: `unfold Whole_Obl_<name>. exists <value>. … frflow_evaluate.`
3. Shared lemmas go in `rocq/Proofs/<Model>/Lemmas.v`, which imports no lemmas of its own; a proof file imports
   them with `Require Export Proofs.<Model>.Lemmas.`
4. A proof file holds only `Require`/`From … Require` and lemmas (`Lemma`, `Theorem`) with tactic proofs between
   `Proof.` and `Qed.`, each tactic line indented or starting with a bullet (no `Axiom`, `Parameter`, `Admitted`,
   `Definition`, `Ltac` or options), and imports only `FrFlowGen.<Model>.Domain`, `FrFlowGen.<Model>.<node>.Spec`,
   `FrFlowGen.<Model>.Whole.Spec`, `FrFlow.Base`, Rocq's `Stdlib`, `Proofs.<Model>.Lemmas`. Only `classic`,
   `constructive_definite_description`, `propositional_extensionality` and `functional_extensionality_dep` may be
   among what a proof rests on.
5. Never prove a step from a contradiction in the parts, or without them.
6. A consistency group FrFlow cannot witness is proven by `Lemma Whole_Proofs_consistent_<i> :
   Whole_Obl_consistent_<i>.` in `rocq/Proofs/<Model>/Whole.v` (importing `FrFlowGen.<Model>.Whole.Spec`), with a
   witness that shows what is assumed can be done.
