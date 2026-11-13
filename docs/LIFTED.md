# Scala compiled into the model: structures and `FrSpec`

The code at the bottom of the refinement graph is given in one of three ways: plain Scala that is tested
(`defineTested`), code written with the DSL that is proven (`define`, `program`), and a class of plain Scala that
is proven (`lifted[Class]`). This document is about the third: a class implementing a trait, compiled into FrFlow's
term language as the model is built. Rocq is printed from the terms and the evaluator runs them; the class stays
the Scala it is, and the JVM runs it.

The idea is the one of [Aeneas](https://github.com/AeneasVerif/aeneas) for Rust (the compiler's view of the program,
translated to a pure lambda calculus, printed for a proof assistant), scoped to what can be held to one meaning in
Scala, in the term and in Rocq.

Statements, and the contracts of types, are written with the DSL: a statement needs `forall` and `exists`, which
have no Scala value, so the one language that says them says everything that is stated. Plain Scala is the code;
the DSL is what is said of it.

## The pipeline

```text
Scala source
   │  scalac (types, overloads, implicits, inlining resolved)
   ▼
class file ──────────────────────────────► the JVM              (what production runs)
TASTy (the class as it was typed, bodies included)
   │  the compiler (`dsl.compiled`), as the model is built: one term operation per construct,
   │  a `NotRead` naming the file and line at any construct it does not read
   ▼
term (`core.term`: FrFlow's typed lambda calculus over the vocabulary; `Expr` is its initial form)
   ├──► the evaluator (`eval.term.Evaluate`)                    (the term's value in Scala)
   └──► the Rocq printer (`proof.rocq`)                         (the definition Rocq proves things of)
```

The term is the AST. It is not a new one: a class is read into the term language every model is written in
(`Sym`, the algebras of `core.term.algebra`), so everything after the compiler is unchanged: validation, the
obligations, the generated modules, the decisions, the fingerprints.

No macro runs where the class is lifted, no Scala is generated, and no compiler option is needed: the input is the
TASTy the Scala compiler wrote beside the class file, so FrFlow never resolves a name or an overload itself.

## What holds the Scala and the term to one meaning

The compiler translates construct by construct, and reads only Scala whose value cannot depend on anything the
term does not have:

- State is the class's own fields, changed by its `update` members; inside a member only `val`s, and only calls of
  the operations listed below and of the members of the structures the class holds. A `lazy val`, a loop, or a
  call of any other method is not read.
- Total: no operation read can throw or fail to end. `head`, `get`, `apply(i)`, division and `throw` are not read; a
  `match` must cover every case of its enum, and has no guard.
- Numbers are `BigInt`, which Rocq's `Z` is. `Int` and `Long` have no `FrSpec`: they wrap around, and `Z` does not.
  An `Int` is read only as a constant given to `BigInt(…)` or as a list's length there.
- Equality is data's. `==` is read between two values of one type whose `equals` is the compiler's (a case class,
  an enum, the standard immutable types), which is Rocq's `=`. `FrSpec.derived` refuses a type that defines its
  own `equals`.
- No value from outside: a member's inputs, the class's fields, its own values, and the methods it calls (their
  bodies read in turn).
- Maps and sets are read at a key or a member, never iterated: their order is not a value of the term.

Since nothing read can fail or diverge, and a member's effect is only its own class's fields, the order Scala
evaluates an expression in cannot be told from the term's value.

**What is still trusted.** The Scala compiler and the JVM, and Rocq's kernel; the compiler of this document, which
is tested and not proven; that inputs are data (no `null`, strings well formed); and the assumptions the developer
accepted. A model's examples are run as Scala on the class (`check` runs them), and are shown by Rocq from the
claims where that proof is written.

## `FrSpec`: a type's spec and contract

Every type a value of compiled code has must have an `FrSpec`. It is the type's `RocqType` (what the type is in the
term language and in the prover) with its contract: the rule every value of the type meets.

```scala
final case class Order(id: OrderId, sku: Sku, units: BigInt, amount: BigInt)

object Order:
  given FrSpec[Order] = FrSpec.derived[Order].where(o => o.units > 0 && o.amount > 0)
```

- `derives FrSpec` (or `FrSpec.derived[T]`) gives a case class or an enum its spec with no contract, as
  `derives RocqType` gives its `RocqType`. The standard types' specs are given (`Boolean`, `BigInt`, `String`,
  `Unit`, and `List`, `Option`, `Set`, `Map`, pairs and `Either` of types that have one).
- An id has a type of its own: `opaque type PaymentId = String` with
  `object PaymentId extends FrSpec.Opaque[PaymentId, String]`, both at the top level of one file. The companion
  makes a value (`PaymentId("p1")`), reads it (`id.value`) and gives the spec, that of the type it is over: Scala
  tells a payment's id from a card's, and the term language and Rocq read each as the string it is.
- `where(v => …)` states the contract with the DSL, over a `Term` of the type: its fields, the DSL's operations,
  `forall` and `exists`. It is what a statement's formula is written in.
- `contractOf[T]` is the contract as a node's formula, `always[T]` of the rule. The developer decides it as any
  statement: an assumption for a type whose values come from outside, a claim for one the code makes (Rocq then
  proves every value the covered code makes meets it, `made_`). From there it is FrFlow's `always[T]`: a hypothesis
  of every statement about such values, and what the tests' generated values meet.

A spec does not put its contract into the model by itself: only the developer's signed decisions do, so a contract
enters when a node states it.

## What the compiler reads

| Scala | Term |
|---|---|
| `true`, `false`, a string constant, `BigInt(3)` | a constant |
| `a && b`, `a \|\| b`, `!a` | `and`, `or`, `not` |
| `a == b`, `a != b` (one type, data) | `eq`, its negation |
| `a + b`, `a - b`, `-a` (read `0 - a`), `<`, `<=`, `>`, `>=` on `BigInt` | `add`, `sub`, `lt`, `le` |
| `if c then a else b` | `cond` |
| `val x = e; body` | `let` |
| `C(a, b)`, `new C(a, b)` (a case class, an enum's case), `Shape.Empty` | `construct` |
| `r.field` | `field` |
| `r.copy(f = v)` | `copy` |
| `x match { case C(a, b) => …; case c: D => …; case _ => … }` (an enum) | `cases` |
| `o match { case Some(x) => …; case None => … }` | `foldOption` |
| `Nil`, `List(a, b)`, `x :: xs`, `xs ++ ys`, `xs :+ x`, `BigInt(xs.length)` | `nil`, `cons`, `append`, `length` |
| `xs.forall`, `exists`, `filter`, `find`, `map`, `flatMap`, `foldLeft`, `contains`, `isEmpty`, `nonEmpty` | the same |
| `None`, `Some(x)`, `o.forall`, `exists`, `map`, `fold`, `getOrElse`, `contains`, `isDefined`, `isEmpty` | options |
| `m.get(k)`, `m.getOrElse(k, d)`, `m.updated(k, v)`, `m.contains(k)` | maps |
| `s.contains(x)`, `s + x`, `s ++ t` | sets |
| `(a, b)`, `p._1`, `p._2` | pairs |
| a call of an `inline def` | its body, where it is called |
| a call of an ordinary method of the developer's (`b.span`, `Rules.free(held, r)`) | its body, where it is called |
| a call of a member of a structure the class holds | a call of that structure's word |
| a lambda given to an operation above | a binder |

[ROCQ.md](ROCQ.md) says how each term reads in Rocq. An ordinary method is read from the TASTy of its own class;
a method that calls itself is a recursion, which is not read. The standard library's methods are never read this
way: only the operations in the table are. Anything else is a `NotRead` at the construct, saying what is not read.

## Services: code that changes a store

A service method that changes state is read the way Aeneas reads `&mut`: the state passed in and returned, with no
state monad. [SEPARATION-SPIKE.md](SEPARATION-SPIKE.md) records the spike that tried it. A service is written as a
structure: a Declaration of a trait, defined by a class.
[The payment stream](../examples/payments/README.md) is a processor over three services, proven through
redelivery, a crash at any step and a second instance; [the shop](../examples/shop/README.md) is a checkout over
two services and an order book, each over a store of its own. The files compile with capture and separation
checking; what uses the checkers is experimental (`-experimental` for the project, or `@experimental` on the
definitions).

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
  nothing must be kept by the compiler; a class in a library's jar is compiled the same way. A type's `FrSpec` is the one its companion gives, found on the class's class loader
  (`Specs`). Each body is compiled once, while the file is open (`Once`); Scala the compiler does not read is a
  `NotRead` there, naming the file and line. It reads what the table above lists, a `match` on an enum or an
  option included (`CompileMatch`).
- The class is read member by member. Its state is a record named as the trait, a field for
  each of the constructor's; each member's body is read into a function of that record. `limits.define(…)`
  gives each member's word its code, and Rocq proves the code meets every claim that mentions the member.
- A class made with other structures is given their words, in the order its constructor takes them:
  `lifted[StreamPaymentHandler](limits, ledger, offsets)`. A call of a member of a structure it holds is a call of
  that word's member, written as a statement of its own in a member that changes the class (`val cost =
  pricing.price(item)`), so in Rocq the class's code is a function of any members that meet the claims on them,
  and it is proven from those claims. One class is given for a trait in a model: the trait's record is that
  class's fields.
- A claim on a structure made of others is said through their interfaces, asked as it has them:
  `ledger.posted(p.id).in(handler.handle(p).after)` is `posted` of the ledger the handler holds, after the call,
  and a structure read as it stands beside its holder (`ledger.total` beside `handler.handle(p)`) is the one
  held. So a trait needs no member for the proofs' sake: `PaymentHandler` has `handle` alone, and what a claim
  needs more than once ("a payment is applied") is a definition in the model. Which structure holds which is said
  where the class is lifted with their words; one read as it stands beside two holders is refused.
- Holding composes, so what is passed to a constructor is reached however far down. A counter's class is given a
  basket, whose class is given a price list: `pricing.price(i).in(counter.ring(i).after)` is the price list of the
  basket the counter holds, and `pricing.price(i)` beside `counter.ring(i)` is the same one as it stands. In Rocq
  it is each holding's word applied in turn (`basket_holds_pricing (counter_holds_basket counter)`), a word being
  the class's field read. `basket.in(state)` is a held structure whole, as its holder has it, for saying the way
  one holder at a time (`pricing.in(basket.in(counter.current))`); a structure held more than one way from a
  holder is refused until the way is said. Such a claim is proven from the claims on what is held, which are
  stated as its parts (`.refines`). The test model is `CounterModel`, proven in `PricesRocqSuite`.
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
state as a claim is). A class that holds it is read and proven from those assumptions. The model is valid; Rocq
does not build it yet, since a structure with no class has no type in the generated modules.

Not built in this shape: `defineTested` for a structure (a class FrFlow cannot read, tested against the claims);
the class's Scala run against the term read from it on generated cases; two classes for one trait in one model; a
member of more than three inputs (two, for its steps).

## Compared with Aeneas, and with Stainless

Aeneas reads Rust's MIR after borrow checking and turns loans into values passed and returned, so the pure
translation of an imperative program is a consequence of the type system. Scala's counterpart is experimental
(capture and separation checking, which the traits of structures use); beyond it purity is a convention. So FrFlow
reads only the Scala that is pure by its form (the list above), and refuses the rest. That is the same trade as
Stainless's "PureScala", with two differences: the proofs are in the repository beside the refinement graph, in
Rocq, and the property proven is not a contract annotation on the function but the claims of the graph above it.

## What is not built yet

1. **The class's Scala run against its term.** The translation of each class is held by how the compiler is built
   and by the examples; a test of each member on generated cases (the Scala's result against the evaluator's of
   the term) is not built.
2. **Recursion.** The term language has no fixed point (iteration is a list's operations). Structural recursion on
   a list or an enum needs one operation added to `core.term` and its three interpreters; general recursion needs
   a measure, stated beside the function.
3. **A function outside a class.** A decision rule that is not a member of a structure is written with the DSL
   (`define`) or tested (`defineTested`). Compiling a plain function from its TASTy, as a class is, is not built.
4. **Members known by their contract.** A method whose body is not read (a class with its own data structure, a
   library's) as an open function of the term language, known to Rocq only by the type's contract, its Scala tested
   against the contract. This is `defineTested`'s meaning, given per member.
5. **More of code that changes state.** Not yet: a class FrFlow cannot read given for a structure and tested
   against its claims, a loop, a failing call, a search for the schedule that breaks a contract, and a contract
   over two calls at once (a call among others is read one call at a time).
6. **More of Scala.** `Int` and `Long` with their bounds proven, strings' operations, tuples taken apart in a
   pattern, generic functions, the rest of the collections.

## Where the code is

| What | Where |
|---|---|
| `FrSpec`, `Contract`, `contractOf` | `modules/dsl/src/main/scala/frflow/dsl/lifted/` |
| `lifted[Class]`, `holding`: a class compiled from its TASTy as the model is built | `modules/dsl/src/main/scala/frflow/dsl/compiled/` (expressions) and `compiled/steps/` (state, steps, members) |
| A structure's Declaration, `Call`, `State` | `modules/dsl/src/main/scala/frflow/dsl/structure/`; `StructureSuite`, `FrSpecSuite` |
| Services proven among other calls | `examples/payments/`, `examples/shop/`; `PaymentsSuite`, `ShopSuite`; the Rocq suites in `frflow.project.services` |
