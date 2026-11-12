# Plain Scala, read: `lifted` and `FrSpec`

This is a third way to write the code at the bottom of the refinement graph, beside plain Scala that is tested
(`defineTested`) and code written with the DSL that is proven (`define`, `program`): plain Scala that is proven.
The developer writes an ordinary Scala function. At compile time FrFlow reads the function's body into a term of
its term language, the same term a `define` builds. Lean is printed from that term and the evaluator runs it, as
before; the function itself stays the Scala it is, and the JVM runs it.

The idea is the one of [Aeneas](https://github.com/AeneasVerif/aeneas) for Rust (the compiler's view of the program,
translated to a pure lambda calculus, printed for a proof assistant), scoped to what can be held to one meaning in
Scala, in the term and in Lean. This document says what is built, how the three are held together, and what is not
built yet.

## What the developer writes

The domain's types state their contracts in Scala, and the code is Scala:

```scala
import frflow.*

/** What the booking form sends: it ends after it starts. */
final case class Booking(room: String, start: BigInt, end: BigInt)

object Booking:
  given FrSpec[Booking] = FrSpec.derived[Booking].where(b => b.start < b.end)

final case class RoomBookings(room: String, bookings: List[Booking]) derives FrSpec

/** Two bookings do not overlap: they are in different rooms, or one ends by the time the other starts. */
val noOverlap = lifted { (a: Booking, b: Booking) => a.room != b.room || a.end <= b.start || b.end <= a.start }

/** The calendar's code: a request is granted when it overlaps no booking held. */
val grantedCode = lifted { (held: RoomBookings, request: Booking) =>
  held.bookings.forall(b => noOverlap(b, request)) }
```

`noOverlap` and `grantedCode` are Scala functions (`noOverlap(a, b)` is a `Boolean`, computed by the JVM), and they
are Definitions given their meaning where they are written, as a `define` is. Statements mention them as any other
Definition, and the model lists the one a Declaration is defined by:

```scala
val granted = Declaration[(RoomBookings, Booking) => Boolean]("whether a request is granted, given its room's bookings")

val bookingsEndAfterStart = Node.assumption("Every booking ends after it starts.")(contractOf[Booking])

val grantWhenNoOverlap = Node.claim("A request is granted exactly when it overlaps no booking of its room.")(
  forall((held: Term[RoomBookings], request: Term[Booking]) =>
    granted(held, request) === held.bookings.forall(b => noOverlap(b, request))))
  .assuming(bookingsEndAfterStart)

val model = FrModel("Calendar")(grantWhenNoOverlap, bookingsEndAfterStart, granted.define(grantedCode))
```

Lean is given these `def`s, printed from the terms read:

```lean
structure Booking where
  room : String
  start : Int
  «end» : Int

@[frflow_defs] def bookingsEndAfterStart (b : Booking) : Prop :=
  (b.start < b.«end»)

@[frflow_defs] def noOverlap (a : Booking) (b : Booking) : Prop :=
  (((¬(a.room = b.room)) ∨ (a.«end» ≤ b.start)) ∨ (b.«end» ≤ a.start))

@[frflow_defs] def grantedCode (held : RoomBookings) (request : Booking) : Prop :=
  (∀ b ∈ held.bookings, (Calendar.noOverlap b request))
```

and proves `grantWhenNoOverlap` of `grantedCode` (`impl`). In rooms the same claim is tested, on generated cases, of
the calendar's plain Scala; here it is proven of the Scala itself. This model is
`modules/testing/src/test/scala/frflow/eval/Calendar.scala`, and `CalendarLeanSuite` runs it through Lean.

Statements stay in the DSL where Scala cannot say them: `forall` over every value of a type has no Scala value. A
contract can be written with the DSL for the same reason (`whereStated`).

## The pipeline

```text
Scala source
   │  scalac's typer (types, overloads, implicits, inlining resolved)
   ▼
typed tree ──────────────────────────────► JVM bytecode        (what production runs: `Lifted.native`)
   │  the reader (`dsl.lifted.Reader`, a macro): one term operation per construct,
   │  a compile error at any construct it does not read
   ▼
term (`core.term`: FrFlow's typed lambda calculus over the vocabulary; `Expr` is its initial form)
   ├──► the evaluator (`eval.term.Evaluate`)                    (the term's value in Scala)
   └──► the Lean printer (`proof.lean.term.LeanTerm`)           (the `def` Lean proves things of)
```

The term is the AST. It is not a new one: lifted code is read into the term language every model is written in
(`Sym`, the algebras of `core.term.algebra`), so everything after the reader is unchanged: validation, the
obligations, the Lean layout, the decisions, the fingerprints. `LiftedSuite` checks that a function read from plain
Scala and the same function written with the DSL have one IR, binder for binder.

The reader runs where the function is written ("locally"): it needs no compiler plugin and no build step, and its
input is the compiler's typed tree, so it never resolves a name or an overload itself.

## How the three are held to one meaning

There are three artifacts for one function: the Scala the JVM runs, the term, and the Lean `def`. Two translations
connect them, and each is held in two ways: by how it is built, and by a check that does not trust how it is built.

### Scala and the term

**By construction.** The reader translates construct by construct, and reads only Scala whose value cannot depend
on anything the term does not have:

- No state and no effect: only `val`s, and only calls of the operations listed below. A `var`, a `lazy val`, a
  statement that is not a value, or a call of any other method is a compile error.
- Total: no operation read can throw or fail to end. `head`, `get`, `apply(i)`, division and `throw` are not read; a
  `match` must cover every case of its enum (the reader checks it), and has no guard.
- Numbers are `BigInt`, which Lean's `Int` is. `Int` and `Long` have no `FrSpec`: they wrap around, and Lean's
  numbers do not. An `Int` is read only as a constant given to `BigInt(…)` or as a list's length there.
- Equality is data's. `==` is read between two values of one type whose `equals` is the compiler's (a case class,
  an enum, the standard immutable types), which is Lean's `=`.
- No value from outside the function: its inputs, its own values, and the functions it calls (other lifted
  functions, and methods whose bodies the reader reads in turn). A constant read from the environment could differ
  between the run Lean is printed in and the run in production.
- Maps and sets are read at a key or a member, never iterated: their order is not a value of the term.

Since nothing read has an effect, can fail or can diverge, the order Scala evaluates in (`&&` stopping early,
arguments left to right) cannot be told from the term's value, so the reader need not model it. What the compiler
adds around the code as written (a value naming an argument given by name, the receiver of an inlined method, the
default for a field a `copy` leaves as it is) is read as the expression it names.

The term is also typed twice: the reader writes it with the DSL's typed operations, so the Scala compiler checks the
term the reader wrote at the type the Scala has (`Term[A]` for an expression of type `A`).

**By test (`testing.Agreement`).** The translation of each function is tested, not trusted: on generated inputs,
each meeting what always holds of its type (the contracts the model states), the Scala the JVM runs gives what the
evaluator gives of the term. A reader that read a construct as a term of another value shows as a case: the
report is the first case the two differ on, with its inputs, what each gave, and the seed and index it was drawn
from (`Agreement.Outcome.Differ`).

`AgreementSuite` runs it on the calendar, and shows that a term that is not the Scala's is found.

### The term and Lean

**By construction.** One printer prints every term (`LeanTerm`), lifted or written with the DSL; FrFlow's own
examples have exercised it since before this branch.

**By test (`testing.Vectors`).** For each generated case, the fact that the code, called on the case's inputs, gives
what its Scala gave is made an example. `check` treats it as any example: the evaluator runs it on the term, and
Lean decides it from the `def` printed (and is asked the opposite too, which it shows only if the `def` contradicts
the Scala). So on the cases drawn the Scala, the term and the Lean `def` are held to one value, case by case
(`CalendarLeanSuite`).

### What is still trusted

- The Scala compiler and the JVM, and Lean's kernel.
- The reader and the printer on the inputs no case reached. `Agreement` and `Vectors` are tests: they find a wrong
  translation with a case, and do not prove its absence. The reader itself is not proven; validating each
  function's translation by proof instead of by test is listed below.
- That the inputs are data: no `null`, strings well formed (Scala's are UTF-16 and may hold a lone surrogate; Lean's
  hold Unicode scalar values).
- The assumptions the developer accepted, as always.

Where the residue matters more than speed, the term can be what production runs: `d.fn(env)` runs a Definition's
term by the evaluator, so nothing rests on the reader at all (Lean and the run then share the term itself).

## `FrSpec`: a type's spec and contract

Every type a value of lifted code has must have an `FrSpec`. It is the type's `LeanType` (what the type is in the
term language and in Lean) with its contract: the rule every value of the type meets.

```scala
final case class Booking(room: String, start: BigInt, end: BigInt):
  inline def length: BigInt = end - start

object Booking:
  given FrSpec[Booking] = FrSpec.derived[Booking].where(b => BigInt(0) < b.length)
```

- `derives FrSpec` (or `FrSpec.derived[T]`) gives a case class or an enum its spec with no contract, as
  `derives LeanType` gives its `LeanType`. The standard types' specs are given (`Boolean`, `BigInt`, `String`,
  `Unit`, and `List`, `Option`, `Set`, `Map`, pairs and `Either` of types that have one).
- An id has a type of its own: `opaque type PaymentId = String` with
  `object PaymentId extends FrSpec.Opaque[PaymentId, String]`, both at the top level of one file. The companion
  makes a value (`PaymentId("p1")`), reads it (`id.value`) and gives the spec, that of the type it is over: Scala
  tells a payment's id from a card's, and the term language and Lean read each as the string it is. Lifted code
  passes such a value on and compares it; it does not make or open one.
- `where(v => …)` states the contract in plain Scala over the value's members: its fields, and its `inline`
  methods. It is read as lifted code is, and kept as the Scala it is: `FrSpec[Booking].holds(b)` checks a value
  where the code runs (at a boundary, where a value comes from outside).
- `whereStated(v => …)` states it with the DSL, for a rule plain Scala cannot say (`forall`, `exists`).
- `contractOf[T]` is the contract as a node's formula, `always[T]` of the rule. The developer decides it as any
  statement: an assumption for a type whose values come from outside, a claim for one the code makes (Lean then
  proves every value the covered code makes meets it, `made_`). From there it is FrFlow's `always[T]`: a hypothesis
  of every statement about such values, and what the tests' generated values meet.

A spec does not put its contract into the model by itself: only the developer's signed decisions do, so a contract
enters when a node states it.

## What the reader reads

| Scala | Term | Lean |
|---|---|---|
| `true`, `false`, a string constant, `BigInt(3)` | a constant | `True`, `"…"`, `(3 : Int)` |
| `a && b`, `a \|\| b`, `!a` | `and`, `or`, `not` | `∧`, `∨`, `¬` |
| `a == b`, `a != b` (one type, data) | `eq`, its negation | `a = b`, `¬(a = b)` |
| `a + b`, `a - b`, `-a` (read `0 - a`), `<`, `<=`, `>`, `>=` on `BigInt` | `add`, `sub`, `lt`, `le` | `+`, `-`, `<`, `≤` |
| `if c then a else b` | `cond` | `if c then a else b` |
| `val x = e; body` | `let` | `let x := e; body` |
| `C(a, b)`, `new C(a, b)` (a case class, an enum's case), `Shape.Empty` | `construct` | the constructor applied |
| `r.field` | `field` | `r.field` |
| `r.copy(f = v)` | `copy` | `{ r with f := v }` |
| `x match { case C(a, b) => …; case c: D => …; case _ => … }` (an enum) | `cases` | `match x with …` |
| `o match { case Some(x) => …; case None => … }` | `foldOption` | `match o with …` |
| `Nil`, `List(a, b)`, `x :: xs`, `xs ++ ys`, `xs :+ x`, `BigInt(xs.length)` | `nil`, `cons`, `append`, `length` | lists |
| `xs.forall`, `exists`, `filter`, `find`, `map`, `flatMap`, `foldLeft`, `contains`, `isEmpty`, `nonEmpty` | the same | `∀ x ∈ xs`, `List.filter`, … |
| `None`, `Some(x)`, `o.forall`, `exists`, `map`, `fold`, `getOrElse`, `contains`, `isDefined`, `isEmpty` | options | `Option` |
| `m.get(k)`, `m.getOrElse(k, d)`, `m.updated(k, v)`, `m.contains(k)` | maps | `K → Option V` |
| `s.contains(x)`, `s + x`, `s ++ t` | sets | `A → Prop` |
| `(a, b)`, `p._1`, `p._2` | pairs | `(a, b)`, `p.1`, `p.2` |
| `f(a, b)` of a lifted `f` | a call of its Definition | `Model.f a b` |
| a call of an `inline def` | its body, where it is called | the body |
| a call of an ordinary method of the developer's (`b.span`, `Rules.free(held, r)`), compiled with `-Yretain-trees` | its body, where it is called | the body |
| a lambda given to an operation above | a binder | `fun x => …` |

### Functions that lifted code calls

- **Another lifted function** (`val noOverlap = lifted { … }`) is called by name: Lean has one `def` for each, so
  the Lean keeps the shape of the Scala, and each can have claims of its own.
- **An `inline def`** is read where it is called: the compiler has put its body there before the reader runs.
- **An ordinary method** of the developer's code (a case class's member, an object's function) is read where it is
  called too, its receiver the body's `this` and its arguments its parameters, when the compiler kept its body: a
  macro is shown the body of a method it is not given only under scalac's `-Yretain-trees`. Without the option the
  call is a compile error that says so. A method that calls itself is a recursion, which is not read. The standard
  library's methods are never read this way: only the operations in the table are.

A lifted function takes one to four inputs. A closed expression is read too (`lifted { noOverlap(a, b) }` with `a`
and `b` written out is a `Term[Boolean]`): an example's fact in plain Scala (`CalendarExamples`).

Anything else is a compile error at the construct, saying what is not read and what to write. `RefusedSuite` holds
each.

## Services: code that changes a store

A service method that changes state is read the way Aeneas reads `&mut`: the state passed in and returned, with no
state monad. [SEPARATION-SPIKE.md](SEPARATION-SPIKE.md) records the spike. It is written two ways. A structure, a
Declaration of a trait defined by a class ("A structure: a value with members" below), is the one to write:
[the payment stream](../examples/payments/README.md) (a processor over three services, proven through redelivery,
a crash at any step and a second instance). The first way, a word and a reading per method, is what
[the wallet](../examples/wallet/README.md) (one service over one store) and
[the shop](../examples/shop/README.md) (a checkout over two services and a store) use, and is described first.

```scala
final class Ledger(var books: Books) extends caps.Mutable:        // a store: its state is its one `var`
  update def claim(request: String): Boolean = …

final class Transfers(ledger: Ledger^):                           // a class holding one store, exclusively
  def transfer(t: Transfer): Outcome = …

object Transfers:
  val transfer = Declaration[(Books, Transfer) -> (Outcome, Books)]("a transfer, alone: …")
  val transferCode = updating { (transfers: Transfers^, t: Transfer) => transfers.transfer(t) }
  val transferAmongOthersCode =
    interleaving { (transfers: Transfers^, t: Transfer) => transfers.transfer(t) }(others)
```

- `updating { (port: P^, input: A) => … }` is a lifted function from the port's state and the input to the result
  with the state after. Its Scala (`native`) makes the stores from the state, runs the method, and gives back
  what the stores hold.
- A port is a store, or a class holding ports. A class holding one port has that port's state. A class holding
  several names its state in its companion, `type State = Pipeline`, a case class with one field for each port
  it holds, in order; a call made on a port reads its field and leaves the state with that field
  replaced.
- `interleaving { … }(others)` is a Definition from the state, a schedule (`Map[BigInt, S]`: what other calls left
  before each step, by the step's number) and the input, to the result with every step taken (the state it started
  from, the state it left). Before each step after the first, the schedule's state replaces the call's own when the
  rely `others(input, before, after)` holds of it. A claim over every schedule is a claim over every interleaving
  the rely allows. Each call of a store's method is one step; that it is atomic is a design node's to say.
- A call of a method of a port the code holds is a call of the Definition of that name in the port's companion,
  when there is one (a method of one argument): the code is then proven from the port's contracts, not from the
  method's body. Read alone, that holds of a store's methods and of those of a class holding ports, so a class
  that calls such classes is proven from their contracts. Read among other calls, such a method is its body, down
  to the stores' methods, each a step. A port's own readings (`updating { (ledger: Ledger^, …) => ledger.claim(…) }`) are its
  methods' bodies. The Definitions' names are the methods', so two ports of one model give their methods
  different names.
- The files compile with capture and separation checking, and the project with `-Yretain-trees`; what uses the
  checkers is experimental (`-experimental` for the project, or `@experimental` on the definitions). In a
  capture-checked file a Definition's function type is written with the pure arrow (`->`).

Three things about the proof side show in these examples:

- A claim that quantifies a value whose type has a contract a node states must bind that value last
  (`forall((books, request, t: Term[Transfer]) => …)`), or the witness FrFlow derives for "its condition can hold"
  is not accepted by Lean and the check stays open.
- FrFlow's search finds no values for the condition of some claims with three or more quantified values; the
  developer then gives them in `Proofs/<Model>/Whole.lean`, as the examples' proofs are given.
- A method read among other calls is a long definition. A hand proof takes it apart with `extract_lets`, and a
  model's proofs share one lemma that walks its steps (`every_step` in the examples' `Lemmas.lean`): each
  contract over every step is then a few lines saying what each store's method keeps.

### A structure: a value with members

A structure is a value with members, some of them functions. A trait says what members it has, a `Declaration` of
the trait's type is the structure in the model, the claims are on that word through its members, and a class that
implements the trait is its Definition. The word is logic's: the trait is a signature, the claims a theory over
it, the class a structure the theory is proven of. A service is written as one.

```scala
trait CardLimits extends caps.Mutable:                                 // the members: nothing of FrFlow's
  update def authorise(p: Payment): Boolean
  def decided(id: String): Boolean

object Limits:
  val limits = Declaration[CardLimits]("the card limits: …")         // the structure in the model
  val authorisedIsRecorded = Node.claim("A payment authorised is decided.")(
    forall((p: Term[Payment]) => limits.decided(p.id).in(limits.authorise(p).after)))

final class RecordedLimits(val dailyLimit: BigInt, var decisions: List[Decision]) extends CardLimits: …   // a value for it

FrModel("Payments")(…, limits.define(lifted[RecordedLimits]))
```

- `Declaration[T]` of a trait of the developer's is typed by the trait's members: each is called in a statement
  as the trait declares it and gives a `Call`. A `Call` is the member's result (`result`); `after` is the
  structure once it is made; `in(state)` makes it on a given state of the structure; called plainly it is made on
  the structure as it stands (`limits.current`). Each member is a word of its own (`limits_authorise`): a
  function of the structure that gives the result, and of an `update` member the structure after it.
- A trait with a member that changes it extends Scala's `caps.Mutable` and marks that member `update`, in a file
  with capture and separation checking. A trait no member changes extends nothing (`trait Pricing { def
  price(item: Item): BigInt }`): it is taken for a structure when it is not sealed, has no `FrSpec` of its own,
  and its members are over domain types. Any other type declared is a plain word.
- A claim is said of the structure in every state: "the structure as it stands" is a variable the claim is closed
  over. So a claim is one that code holding the structure can rely on, whatever state it holds it in; and a fact
  of every state ("no card is over its limit") is stated as what each call keeps.
- `lifted[RecordedLimits]` compiles the class from the TASTy the Scala compiler wrote beside its class file, as
  the model is built. TASTy is the class as it was typed, bodies included. FrFlow's compiler (`dsl.compiled`)
  opens the file (`Inspect`, over `scala3-tasty-inspector`, which a project that builds a model names as a
  dependency), walks each member's tree, and builds the member's term: one operation of the term language for
  each Scala construct it reads. No macro runs where the class is lifted, no Scala is generated or compiled, and
  nothing must be kept by the compiler (`-Yretain-trees` is not needed for it); a class in a library's jar is
  compiled the same way. A type's `FrSpec` is the one its companion gives, found on the class's class loader
  (`Specs`). Each body is compiled once, while the file is open (`Once`); Scala the compiler does not read is a
  `NotRead` there, naming the file and line. It reads what the table above lists, a `match` on an enum or an
  option included (`CompileMatch`); a call of a `lifted { … }` function from a class is not read yet.
- The class is read member by member. Its state is a record named as the trait, a field for
  each of the constructor's; each member's body is read into a function of that record. `limits.define(…)`
  gives each member's word its code, and Lean proves the code meets every claim that mentions the member.
- A class made with other structures is given their words, in the order its constructor takes them:
  `lifted[StreamPaymentHandler](limits, ledger, offsets)`. A call of a member of a structure it holds is a call of
  that word's member, written as a statement of its own in a member that changes the class (`val cost =
  pricing.price(item)`), so in Lean the class's code is a function of any members that meet the claims on them,
  and it is proven from those claims. One class is given for a trait in a model: the trait's record is that
  class's fields.
- A claim on a structure made of others is said through their interfaces, asked as it has them:
  `ledger.posted(p.id).in(handler.handle(p).after)` is `posted` of the ledger the handler holds, after the call,
  and a structure read as it stands beside its holder (`ledger.total` beside `handler.handle(p)`) is the one
  held. So a trait needs no member for the proofs' sake: `PaymentHandler` has `handle` alone, and what a claim
  needs more than once ("a payment is applied") is a definition in the model. Which structure holds which is said
  where the class is lifted with their words; one read as it stands beside two holders is refused.
- A member that changes the structure takes steps: a class that holds no structure makes its change in one, a
  class made of structures takes one for each call it makes of them (a query too). `call.steps` is each step that
  changes the structure, as the step found it and as it left it; a crash leaves the structure as one of them did.
  `call.among(between)` is the call made among other calls, which leave the structure as `between` says before a
  step, by the step's number (any state at all: no rely is built in); `call.amongOthers(run => …)` says what holds
  under every such schedule; `run.others` is what the others did before each step, for a claim to say what it
  takes of them. What it takes, a claim over the structure's own steps shows it grants.
- An example gives a state as an object of the class:
  `limits.holding(RecordedLimits(BigInt(100), Nil))`, and a schedule as `limits.nobody.updated(BigInt(2), left)`.
  The evaluator holds a state as its fields' values, so two states are equal when their fields are.
- A member no claim mentions has its code (an example may call it), and nothing is proven of it.
- A structure's states are typed by the structure's name (`limits.State`, `limits.Schedule`), not by its trait:
  Scala's capture checking reads a `caps.Mutable` trait named in a type as a capability.

A structure no class is read for is `provided` (`ledger.provided`, listed in the model as a Definition is): one
from a library or behind a remote call, known by what is assumed of it (`Node.assumption`, said of it in every
state as a claim is). A class that holds it is read and proven from those assumptions. The model is valid; Lean
does not build it yet, since a structure with no class has no type in the Lean model.

Not built in this shape: `defineTested` for a structure (a class FrFlow cannot read, tested against the claims);
the class's Scala run against the term read from it on generated cases (`Agreement`); two classes for one trait in
one model; a member of more than three inputs (two, for its steps).

## Compared with Aeneas, and with Stainless

Aeneas reads Rust's MIR after borrow checking and turns loans into values passed and returned, so the pure
translation of an imperative program is a consequence of the type system. Scala has no such discipline to lean on:
purity is a convention. So this branch reads only the Scala that is pure by its form (the list above), and refuses
the rest at compile time. That is the same trade as Stainless's "PureScala", with two differences: the proof
assistant is Lean, with the proofs in the repository beside the refinement graph, and the property proven is not a
contract annotation on the function but the claims of the graph above it.

Like Aeneas, each lifted function is one `def` of the prover's, called by name where another calls it, so the Lean
keeps the shape of the Scala.

## What is not built yet

In the order they would be taken:

1. **`check` runs `Agreement` and `Vectors`.** Today they are library functions the suites call. The model does not
   carry lifted code's Scala to the elaborated theory yet; with it there, `check` reports each lifted function as
   "proven; its Scala agrees on N cases", and keeps the failing case as it keeps a claim's.
2. **Recursion.** The term language has no fixed point (iteration is a list's operations). Structural recursion on
   a list or an enum needs one operation added to `core.term` and its three interpreters, printed as a Lean `def`
   by structural recursion; general recursion needs a measure, stated beside the function.
3. **A `def` as its own Lean `def`, and no compiler option.** An ordinary method is read where it is called, when
   the project compiles with `-Yretain-trees`; so its body is repeated in Lean at each call, and it has no claims
   of its own unless it is a lifted `val`. A compiler plugin reading whole files, as Aeneas's Charon reads a crate,
   would give each `def` its Lean `def` with no marking and no option.
4. **Members known by their contract.** A method whose body is not read (a class with its own data structure, a
   library's) as an open function of the term language, known to Lean only by the type's contract, its Scala tested
   against the contract. This is `defineTested`'s meaning, given per member by the type's `FrSpec`.
5. **More of code that changes state.** Service methods over stores, and over other services, are read
   ("Services" above). Not yet: a class FrFlow cannot read given for a structure and tested against its claims, a
   loop, a failing call, a search for the schedule that breaks a contract, and a contract over two calls at once
   (a call among others is read one call at a time).
6. **More of Scala.** `Int` and `Long` with their bounds proven, strings' operations, tuples taken apart in a
   pattern, generic functions, the rest of the collections.
7. **Validation by proof.** For this fragment the reader could emit, per function, the claim that the term's value
   is the Scala's, checked by a second, independent reading (of TASTy, after compilation) instead of by tests.

## Where the code is

| What | Where |
|---|---|
| `FrSpec`, `Contract` | `modules/dsl/src/main/scala/frflow/dsl/lifted/` |
| `lifted`, `contractOf` (the facade's names) | `LiftSyntax.scala` there |
| The reader | `Reader.scala`, `Reading.scala` and `Read*.scala` there |
| `Lifted`, the Definition with its Scala | `Lifted.scala` there |
| `Agreement`, `Vectors` | `modules/testing/src/main/scala/frflow/testing/` |
| The suites | `modules/dsl/src/test/scala/frflow/dsl/lifted/`, `AgreementSuite`, `CalendarSuite`, `CalendarLeanSuite` |
| `updating`, `interleaving` | `modules/dsl/src/main/scala/frflow/dsl/lifted/steps/` |
| `lifted[Class]`, `holding`: a class compiled from its TASTy as the model is built | `modules/dsl/src/main/scala/frflow/dsl/compiled/` (expressions) and `compiled/steps/` (state, steps, members) |
| A structure's Declaration, `Call`, `State` | `modules/dsl/src/main/scala/frflow/dsl/structure/`; `StructureSuite` beside the reader's suites |
| Services proven among other calls | `examples/wallet/`, `examples/payments/`, `examples/shop/`; `WalletSuite`, `PaymentsSuite`, `ShopSuite`; the Lean suites in `frflow.project.services` |
