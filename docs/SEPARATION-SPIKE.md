# Spike: Scala that changes a port, read under separation checking

A spike on top of [LIFTED.md](LIFTED.md). It asks whether service code, which changes state, can be read the way
Aeneas reads Rust's `&mut`: with no state monad, the state passed in and returned, and the exclusivity that makes
that sound checked by the Scala compiler (capture checking with separation checking, experimental in Scala 3.10).

## What was tried

```scala
import language.experimental.captureChecking
import language.experimental.separationChecking

/** A port: its state is its one `var`; reading is an ordinary method, changing it an `update` method. */
final class Table(var rows: List[Booking]) extends caps.Mutable:
  def inRoom(room: String): List[Booking] = rows.filter(b => b.room == room)
  update def add(b: Booking): Unit = rows = rows :+ b

/** A service method in direct style over a port it has to itself (`Table^`). */
val book = updating { (table: Table^, request: Booking) =>
  val held = table.inRoom(request.room)
  val ok = free(held, request)
  if ok then table.add(request)
  ok }
```

`updating` (`dsl.lifted.steps`) reads the method into a function of the port's state that gives its result with the
state after it, a lifted function as any other. Lean is given (its parentheses and type
annotations left out here):

```lean
def book (table : List Booking) (request : Booking) : Prop × List Booking :=
  let held := List.filter (fun b => decide (b.room = request.room)) table
  let ok := Desk.free held request
  let after := if ok then (let rows := table ++ [request]; ((), rows)) else ((), table)
  (ok, after.2)
```

The reading: the port's variable stands for its state; a call of an `update` method is the state its body leaves; a
`var`'s assignment is the value assigned; what follows a change reads the new state; an `if` that changes the state
gives the state either branch leaves. Nothing of FrFlow's `Flow`, `Prog` or `StateModel` is used.

## What works

1. **The macros compile beside the checkers.** `lifted`, `derives FrSpec` and `updating` compile in files with both
   checkers on, under the build's `-Werror` (`dsl`'s `sep` tests, `frflow.eval.Desk`).
2. **A service method is proven end to end.** `DeskLeanSuite`: the desk's two claims (what it answers, what the
   table holds after) are proven by FrFlow's automation of the `def` above, and what the Scala gives on generated
   cases Lean decides from it (`Vectors`).
3. **The Scala agrees with the term.** `DeskSuite`: the method, run on a table made from the rows, gives the result
   and rows the evaluator gives of the term, on 300 generated cases (`Agreement`, unchanged).
4. **An ordinary `def` is read by reference.** `def reserve(table: Table^, request: Slot): Boolean` stays the
   developer's method, called by checked code with its own types; `updating { (t: Table^, r: Slot) => reserve(t, r) }`
   reads its body (with `-Yretain-trees`).
5. **Separation checking is active in those files.** Checked by compiling wrong code beside the macros: a port given
   twice to exclusive parameters is a "Separation failure", an `update` through a reference that only reads is
   refused ("its capture set {t} is read-only").

## What was found

1. **A port cannot carry a type class of FrFlow's.** `derives FrSpec` on a `Mutable` class does not type-check
   (`FrSpec[Table^{}]` found, `FrSpec[Table^{any.rd}]` required): FrFlow is not capture-checked, and its type classes
   are invariant. So a port is not data: its *state* is data with an `FrSpec`, and the port has a witness of its
   state's type the compiler finds (`PortState`).
2. **FrFlow's own function types lose the capability.** A function value FrFlow hands back over the port would be
   typed `(Table^{}, Booking) => Boolean`, so checked code could not give it an exclusive `Table^`. The service
   method stays the developer's `def` (what works, 4); what `updating` gives is a function of the port's state.
   For the same reason a `Definition`'s function type is written with the pure arrow (`->`) in a checked file.
3. **Experimental marking spreads.** Under `-experimental` every definition of a module is experimental, and a
   module using it without the flag does not compile. Marking the definitions written with the checkers
   (`@experimental`), and what uses them, needs no flag; the spike does that.
4. **`IO`-style code is not protected.** The same method written as a `for` over cats-effect's `IO` compiles, but
   the checker does not see a port held inside an `IO` value: two programs built over one exclusive table, with the
   table changed between, compile with no error. cats-effect is not capture-checked. Direct style is checked.
5. **Two compiler details.** A derived type's name was read as `Slot @inferred` under capture checking (fixed in
   `DataMacros.named`). `compiletime.testing.typeCheckErrors` does not run the checkers, so a suite cannot assert a
   separation error; those were checked by compiling.

## What the spike does not cover

- One port, whose state is one `var` given to its constructor, and one input. No second port (see "Since the
  spike"), no port given on to other code: the cases where exclusivity is needed for the reading to be right. With one port the reader's own limits already rule aliasing out, so the spike shows the checker beside
  the reader, not yet a reading that depends on it.
- A port that is its own model. A port with an adapter (SQL behind a trait) needs its model given apart, and the
  adapter tested against it, as `implementTested` does for a store's operations.
- No loop, no change inside a function given to an operation, no failure (Aeneas's `Result`). Concurrency is read
  as one call among others under a rely ("Since the spike"), not as threads.
- The world outside: another process writing the same store is an assumption, as it is today.
- `check` knows nothing of it; `Agreement` and `Vectors` are called by the suites.

## What it suggests

Reading services in direct style, state passed and returned, is workable, and the `update` marker and exclusive
parameters of Scala's checkers give the reader what Rust's `&mut` gives Aeneas. The next step that would test the
idea is a service class holding two ports, where the reading is only right because separation is checked; then a
port with an adapter; then failure. `IO`-style services would need a capture-checked effect type, or stay outside
what is read.

## Since the spike

[The wallet example](../examples/wallet/README.md) takes the next steps on one store. A port may be a service class
holding a store in a field. A service's call of a store's method is read as a call of the Definition of that name
in the store's companion, so the service is proven from the store's contracts. And `interleaving` reads a method
among other calls: before each step after the first, a schedule may replace the store's state with one a rely
admits, and the reading gives every step taken; contracts proven for every schedule rule out the check-then-act
race the example's second service has.

[The shop](../examples/shop/README.md) takes the step this spike named next: a service holding several ports.
([The payment stream](../examples/payments/README.md) is written the way that followed: each service a
`Definition` of a trait, given the class that implements it; [LIFTED.md](LIFTED.md) "A service as a Definition".) Its state is a case class its companion names (`type State`),
one field per port, and a call on a port leaves the state with that field replaced; that two ports are two
stores, never one reached twice, is what separation checking says of the class. Read alone, a call of another
service is a call of its Definition, so a processor over three services is proven from their contracts. Still
not covered: an adapter, loops, failure.

Where it is: `modules/dsl/src/main/scala/frflow/dsl/lifted/steps/`, the suites `dsl`'s `lifted.sep.SepSuite`,
`frflow.eval.DeskSuite` and `frflow.project.services.DeskLeanSuite`, and the model `frflow.eval.Desk`.
