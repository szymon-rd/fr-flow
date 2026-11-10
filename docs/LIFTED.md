# Plain Scala, read: `lifted` and `FrSpec`

This is a third way to write the code at the bottom of the refinement graph, beside plain Scala that is tested
(`implementTested`) and code written with the DSL that is proven (`define`, `program`): plain Scala that is proven.
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
Definition, and the model gives them to a Definition with `implementProven`:

```scala
val granted = Definition[(RoomBookings, Booking) => Boolean]("whether a request is granted, given its room's bookings")

val bookingsEndAfterStart = Node.assumption("Every booking ends after it starts.")(contractOf[Booking])

val grantWhenNoOverlap = Node.claim("A request is granted exactly when it overlaps no booking of its room.")(
  forall((held: Term[RoomBookings], request: Term[Booking]) =>
    granted(held, request) === held.bookings.forall(b => noOverlap(b, request))))
  .assuming(bookingsEndAfterStart)

val model = FrModel("Calendar")(grantWhenNoOverlap, bookingsEndAfterStart).implementProven(granted)(grantedCode)
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
and `b` written out is a `Term[Boolean]`): an example's fact in plain Scala.

Anything else is a compile error at the construct, saying what is not read and what to write. `RefusedSuite` holds
each.

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
   against the contract. This is `implementTested`'s meaning, given per member by the type's `FrSpec`.
5. **Effects.** A program's steps in plain Scala (`for`-comprehensions over a store's operations) read into
   `Prog`, as `program { … }` records them today.
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
| The suites | `modules/dsl/src/test/scala/frflow/dsl/lifted/`, `AgreementSuite`, `CalendarLeanSuite` |
