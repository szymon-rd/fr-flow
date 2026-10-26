# FrFlow: architecture of the rebuild

This is the approved design of FrFlow's rebuild; `review.md` is the approving review. It says what the design is, not
how it was reached. The revision log it was first written as is kept in `history/ARCHITECTURE-r15-log.md`;
`history/MAPPING.md` says where each of its sections went.

Beside this file, in `docs/redesign/`:

| File | What it holds |
|---|---|
| `owner-decisions.md` | the owner's decisions, cited here as "owner §n" |
| `review.md` | the approving review, kept as written (its paths are the design workspace's) |
| `features.md` | every feature of today's library, its concept here, its use, what the rebuild does |
| `dependencies.txt` | today's package and module dependencies, measured |
| `planned/` | the planned code: nine of the twelve modules, compiled, with suites |
| `lean-spike/` | rooms' and auth's Lean as the printer gives it, built by `lake`, with proofs |
| `tools/budget.py` | the size budgets, measured over `planned/` |

Source paths below are under `planned/src/<module>/`; rooms is `planned/test/project/frflow/rooms/`, auth
`planned/test/project/frflow/auth/`.

## 1. Summary

### 1.1 What FrFlow is, and what is wrong today

FrFlow is a compiler. It reads a model written in a Scala DSL, checks it, and produces Lean files to prove, Scala to
run, and property tests. Around that sits a ledger of the developer's signed decisions about each statement. Today's
code (12,008 main lines) does all this but is not organised as a compiler: no IR between phases (what a term mentions
is learned by printing it); a string-typed Lean back end; one `Node` class (24 fields) for six kinds and a 52-member
`KnowledgeBase`; a core that depends on the wire format; package cycles everywhere; the same concept represented in
two to five classes (a Lean type, a test report, "proven, tested or assumed"); what the developer decides cut out of
the source text by line heuristics, so a comment edit reopens a node; and `IDEA.md` stating the purpose a second time.
Appendix B lists the seventeen measured problems and where each is addressed.

### 1.2 What it becomes

1. **The owner's concepts, and no others** (owner §15): three kinds of nodes, two kinds of values, two quantifiers,
   two edges. How a claim is checked is derived and shown. The theory is proven consistent and not vacuous; examples
   are tests beside it; the world outside is said by assumptions.
2. **A compiler with a type per stage**: DSL, `Elaborated`, `Valid`, `Resolved`, `Prop`, `LeanModule`, text; every
   phase pure.
3. **Tagless-final terms**: one printer (Lean) and one evaluator (Scala); the IR read only by analyses; the user
   writes a closed `Term[A]`.
4. **Tagless programs over boundaries**, recorded for Lean, run in `IO` in production.
5. **No run-time checking**: Lean and property-based tests, before production only.
6. **No ambient state**: plain code is given its values; a variable is named by the interpreter that binds it.
7. **Decisions as a pure module**, with a committed signed list of who may decide; ledgers start fresh.
8. **Effects as algebras only where they pay**; the core takes no `F`.
9. **Twelve modules**, each its own top package, checked by a build test.
10. **A code fingerprint over Scala as a simple lexer reads it.**

### 1.3 Recommendation

Rebuild FrFlow from the planned code in this repository, beside today's modules (section 9): the new modules in
dependency order, then the examples one at a time, smallest first (rooms, auth, keycloak, crm, sharing), each with a
fresh ledger; delete today's modules once the last has moved. Today's outputs are recorded once as a reference: each
ported example must have every claim proven and every seeded bug caught, and the README's rooms walk-through must
reproduce; where output differs, the difference is listed and judged. The owner decides each new ledger at the end.

### 1.4 What is already shown

- The planned code (449 main files, 10,340 lines; 57 test files, 147 tests) compiles from clean with
  `-Werror -Wunused:all -Wnonunit-statement -Wvalue-discard`, and every test passes. 40 `???` in 31 files stand for
  ports of today's code, each assigned a step of the plan, its parts written and tested.
- `budget.py`: no file over 200 lines, no line over 120 columns, no parameter list over four, one type per file.
- Lean 4.35.0 builds rooms' and auth's modules as printed (`lean-spike/`): eighteen theorems, no `sorry`, axioms
  `propext`, `choice`, `Quot.sound` only.
- Four of crm's generated Lean files print byte for byte from the new Lean AST.

```sh
cd docs/redesign/planned
sbt clean compile proof/test decision/test dsl/test project/test evaluation/test testing/test
```

### 1.5 Reading the planned code

In this order, under `planned/src/` unless a suite:

1. rooms' `Rooms.scala`, `Book.scala` and `Knowledge.scala` (`planned/test/project/frflow/rooms/`): a model as the
   user writes it;
2. `core/frflow/core/spec/Statement.scala`, `Range.scala`, `CallForms.scala`: what a node says, and its readings;
3. `dsl/frflow/dsl/vocab/Definition.scala` and `Stating.scala`: the two kinds of values;
4. `core/frflow/core/term/Sym.scala` and `interpret/Forward.scala`: the term algebras and the transformer base;
5. `proof/frflow/proof/lean/term/LeanTerm.scala` and `eval/frflow/eval/term/Evaluate.scala`: the one printer and the
   one evaluator;
6. `core/frflow/core/analysis/Validate.scala`: the structural rules;
7. `core/frflow/core/consistency/Consistency.scala`: groups and witnesses;
8. `proof/frflow/proof/obligation/Required.scala`: what Lean is asked of each node;
9. `decision/frflow/decision/rules/Decide.scala`: one rule per command;
10. the suites `BookSuite` and `CalendarSuite` (rooms' tests): what is shown.

## 2. The concepts

Each concept: a definition, an example from the planned rooms model, and how FrFlow checks it. Section 3 shows the
whole model; the names used before it: a `Booking` has a room, a start and an end; `RoomBookings` is a room's bookings
as the store gives them; `stored` is the store's model, holding every booking; `book` is the booking program and
`granted` the calendar's decision on a request; `apart` and `noOverlap` say two bookings share no time (over moments,
and over start and end times); `isFree` says a request is apart from every booking held; `bookWhenFree` is the root
claim about `book`; `storeModel`, `oneAtATime` and the other premises are the assumptions of 2.6.

### 2.1 Nodes: claim, assumption, design

A node is `Node(id, says, statement)` (`core.spec`): its id is its val's name as written, `says` its sentence. It has
no reason field; why it holds is the reason of its signed decision. What it says has three cases
(`core/frflow/core/spec/Statement.scala`):

```scala
enum Statement:
  case Claim(formula: Written[Expr], reliance: Reliance)
  case Assumption(formula: Written[Expr])
  case Design(governs: NonEmptyList[RelPath])
```

A **claim** is proven, or tested where a Definition it mentions is plain Scala. An **assumption** is trusted: the
world outside the code, or an outside system's promise. A **design** is a decision about code no proof covers, naming
the files it governs. The DSL forms are `Node.claim(statement)(formula)`, `Node.assumption(statement)(formula)` and
`Node.design(statement)(paths*)`; a formula is a context function `Stating ?=> Term[Boolean]`.

```scala
val grantWhenFree = Node.claim("A request is granted exactly when its room is free for its whole time.")(
  forall((held: Term[RoomBookings], request: Term[Booking]) =>
    granted(held, request) === isFree(held.bookings, request)))
  .refines(bookWhenFree)
```

There is no contract, invariant, model or definition node under any name; those forms do not compile (`FormsSuite`),
and section 8 says what replaced each. A claim is checked by what its formula and the meanings of what it mentions
derive (2.7). `.leftOpenAbove` (`Reliance.LeftOpen`) is a claim's only. One idea per statement is a style guide, not a
check (owner §10, §16). Renaming a val renames its node, a new node to decide; `.replaces(old)` links the two.

### 2.2 Values: Declaration and Definition

A **Declaration** is an abstract value of any type, known only through the statements about it. It is not a `Term`, is
never implemented, and is applied only where a statement is written: its `apply` asks for a `Stating`, which only
`Node.claim`, `Node.assumption` and `example` give, so code naming it does not compile. Auth's purpose is about three;
two of them (`Auth.scala`):

```scala
val access = Declaration[(UserId, Path) => Boolean]("whether the system lets the user reach the path")
val signedIn = Declaration[UserId => Boolean]("whether the user has signed in")
```

The message a Declaration in code gets (`dsl/frflow/dsl/vocab/Stating.scala`):

```scala
@implicitNotFound("FrFlow: a Declaration is used only in statements (Node.claim, Node.assumption, an example); " +
  "code, defines and programs use Definitions")
sealed trait Stating
```

A **Definition** is a value code and programs use, of any type (a function, a program over a store, a plain value). It
is a `Term` and gets its meaning exactly once, in the knowledge base or where it is written:

```scala
val granted = Definition[(RoomBookings, Booking) => Boolean]("whether a request is granted, given the room's bookings")
```

| Written | `core.code.Code` | Claims mentioning it are |
|---|---|---|
| `implementProven(d)(p)` | `Proven`, `ProvenFlow` | proven of `p` in Lean (`impl`) |
| `implementTested(d)(env => code)` | `Tested` | tested on generated cases |
| `implementValue(d)(v)` | `Valued` | stated with `v` substituted |
| `implementProvided(d*)` | `Provided` | stated for every value provided |
| `define { … }`, `program { … }` | `Proven`, `ProvenFlow` | proven, the meaning given on the spot |

A provided value is bound by an example, drawn by a test, passed in production. `define` (to six inputs) and `program`
return a Definition carrying its meaning (`Definition.onTheSpot`); a define is called by name (`covers(b, t)`), passed
as a function (`held.pairwise(apart)`), and run in plain code by the evaluator (`d.fn(env)`). Plain code reads a
Definition's value with `env(d)`; a Declaration has none.

Elaboration and validation check what the types cannot: a meaning given twice (`Fault.MeantWhereWritten`),
`implementProven` of no define or program (`NotProvenCode`), a program named in a claim (`ProgramMentioned`), a
Definition with no meaning (`Problem.Undefined`), a Declaration reached from proven code through a helper
(`DeclarationInCode`), code no claim mentions (`CodeWithoutClaim`), a statement mentioning a Definition with no Lean
type (`CodeOnlyInStatement`). In the core, `vocab.ValueKind` is `Declaration` or `Definition`; a define's body is
`term.Body`.

### 2.3 Quantifiers: forall and always

`forall` ranges over every possible value; `always[T](x => …)` over every value of `T` that can be made;
`always(stored)(s => …)` over every state the store reaches. What a statement ranges over is read off its formula
(`core/frflow/core/spec/Range.scala`):

```scala
enum Range:
  case Possible
  case Made(ty: Ty)
  case Reached(models: List[ModelName])
```

What always holds is its own claim, never glued into another with `&&`; its rule becomes a define named as the node:

```scala
val endsAfterStart = Node.claim("Every booking ends after it starts.")(always[Booking](b => b.start < b.end))
  .assuming(fromTheForm, storeModel, oneAtATime, startsEmpty, onlyBookingWrites)

val neverOverlap = Node.claim("The bookings held never overlap.")(always(stored)(held => held.pairwise(apart)))
  .assuming(storeModel, oneAtATime, startsEmpty, onlyBookingWrites)
```

Checked before production only:

- **`always[T]`** is a hypothesis in Lean on every value of `T` a statement is about, including list elements, record
  fields and a world's store (`Guarded`, its guards built by `Guards` from the type). It is met wherever FrFlow covers
  the code: `made_<maker>` for each proven define and store operation whose result is or holds a `T`; `cover_<op>` for
  each program writing a store that holds one; at a tested Definition's boundary (inputs drawn meeting it,
  `Respecting`; result checked, `Made`); `start_<node>` for the store's start; values from outside by
  `outside.calls(d)`. `inhabited_<node>` shows the rule admits a value.
- **`always(stored)`** is a hypothesis on every world a claim starts from, kept by each program writing the store
  (`cover_<op>`) from every start (`start_<node>`); that this covers every reached state rests on four store facts
  (2.6).

For an `always` A, each `H` below being every `always`'s guard on the variable:

| Obligation | States | Asked of |
|---|---|---|
| `cover_<op>` | every run from a world meeting every `always`, on inputs meeting theirs, ends in one meeting A | each program writing a store A is about |
| `made_<maker>` of a define `d` | `∀ x₁ … xₙ, H(x₁) → … → H(xₙ) → A(d x₁ … xₙ)` | each proven define whose result A applies to |
| `made_<maker>` of a store operation | `∀ p (w : World), H(p) → H(w) → A(op_of p w.s)` | each store operation on its model whose result A applies to |

`op_of p s` is `Id.run ((Stored.op p).run' s)`. `made_` is the soundness side of assuming `always[T]` of every value.

A rule met by generated values needs a Scala value, since draws and the witness search use the evaluator; so rooms
states `roomBookingsApart` in start and end times and proves its link to `neverOverlap`'s moments in Lean
(`room_apart` in `lean-spike/Proofs.lean`).

### 2.4 Edges

```scala
enum Edge:
  case PartOf(part: NodeId, whole: NodeId)
  case Assumes(node: NodeId, premise: NodeId)
  case Replaces(alternative: NodeId, original: NodeId)
```

`.refines(parent)` makes a part: the parent is proven from its parts. `.assuming(premise)` makes a premise, the one
mechanism for one: an assumption or a claim of `always` the proof assumes (`Problem.PremiseNotAssumed` otherwise),
never a part, so `impl` and the view's parts leave it out. `.replaces(original)` is a decision's link to an
alternative. A fact about the outside is never a part (`OutsideAsPart`) and only an assumption says one
(`OutsideClaimed`).

### 2.5 Root statements

The root statements are the claims without parents: several are allowed, on any Definitions and Declarations, a
statement relating them included (owner §11). Keeping them a concise few is the author's job, which the agent's skill
says. Validation requires at least one (`NoRoot`), never an assumption, and an acyclic graph whose edges stay inside
it (`DuplicateId`, `AboveItself`, `ParentOutside`, `DesignWithoutParent`, `UnderDesign`). Rooms has five: booking's
two claims and its three claims of `always`.

### 2.6 Assumptions about the world outside

What the world outside the code does is expected to be assumed: the company's procedures, the outside services and how
they are run (owner §16). Each fact is an assumption node, reviewed like any other, written with one of five formulas
(`core.expr.OutsideFact`). Lean does not state them as formulas: its model of the world is built on them.

| Formula | Says | The rule resting on it |
|---|---|---|
| `store.behavesAs(stored)` | the store does what its model does | code is proven on the model; adapters tested against it |
| `stored.initially(held => …)` | what the store's start meets | `start_<node>`: `∀ s, initially s → A s` |
| `stored.writtenOnlyBy(book)` | only these programs change it | every reached state is one a listed run leaves |
| `stored.changedOneRunAtATime` | runs changing it never interleave | each run is one step of the world |
| `outside.calls(book)` | `book` is called with values that can be made | an entry Definition's inputs meet each `always[T]` |

```scala
val storeModel = Node.assumption("The store gives a room's bookings oldest first, and adds one last.")(
  store.behavesAs(stored))

val startsEmpty = Node.assumption("The store starts with no bookings.")(stored.initially(held => held === Nil))

val onlyBookingWrites = Node.assumption("Only booking writes the store: no other program or person changes it.")(
  stored.writtenOnlyBy(book))

val oneAtATime = Node.assumption("Bookings are processed one at a time: one server process runs each atomically.")(
  stored.changedOneRunAtATime)

val fromTheForm = Node.assumption("Requests come from the booking form, which refuses one ending before it starts.")(
  outside.calls(book))
```

Checked: which facts a check rests on is derived (`Premises`), only to check the `.assuming` list the source writes. A
claim about a program's runs on a store rests on `behavesAs` and `changedOneRunAtATime`; an `always(stored)` also on
`initially` and `writtenOnlyBy`; an `always[T]` on `outside.calls(d)` for each entry Definition taking a `T` and on
the facts of each store holding or making one. A missing fact is refused, naming it and the assumption that says it
(`PremiseMissing(id, needs, by)`), as is one not needed (`PremiseNotNeeded`) and an unlisted writer
(`WriterNotListed`). Atomicity is assumed this way (owner §17); asynchrony is future work.

### 2.7 How a claim is checked

A claim constrains every Declaration and Definition it mentions, through its defines too (`Constrained.of`). Its
obligations follow from its formula and from what gives each Definition its meaning:

| When the claim | It gets |
|---|---|
| has parts and no proven code | `complete` (its parts give it), and the tries |
| mentions a Definition with proven code | `impl`: the code meets it |
| mentions a Definition with plain Scala | generated cases, per call or the formula whole |
| mentions a fixed or provided Definition | stated for that value, or for every value provided |
| is an `always[T]` | a hypothesis; `cover_<op>`, `made_<maker>`, `start_<node>`, `inhabited_<node>` |
| is an `always(stored)` | a hypothesis on every world; `cover_<op>` per writer; `start_<node>` |
| is at the bottom (no parts) | a consistency group with what shares its open values (2.8) |
| has a condition `A` in `A implies B` | `satisfiable_<i>_<node>` (2.9) |
| rests on the world outside | its `.assuming` list, checked (2.6) |

`impl` is the step of a node whose code is proven (a define, or a program whose run on the models, `f_run`, stands for
the Definition): "∀ U, H → claim[d := code]", `H` its parts (each a claim about what the code calls, else
`PartNotCalled`) or, with no parts, the claims on what its code calls (`Resolved.reliesOn`). `complete` is not asked
of it.

**A claim read as a call.** Where a claim applies one Definition to exactly its leading `forall` variables (alone, or
one side of its equation) and mentions it nowhere else, `CallForms` reads it as a call; a program's claim
`forall((request, before) => book(request).from(before) { (booked, after) => … })` reads as a run, with a failure
clause where it states one (`.failing { (error, after) => … }`, `.failsChangingNothing[E]`). Another Definition on
the same variables is an ordinary mention.

```scala
enum CallForm:
  case Call(op: SymbolName, post: Written[Lambda])
  case Run(op: SymbolName, post: Written[Lambda], failure: Option[FailureClause])
```

The post is the formula with its leading `forall`s opened (`Opened`): a lambda over the call's inputs (for a run, its
result and worlds too), the Definition a symbol given the call's result when checked. A claim that reads as no call is
tested by evaluating the whole formula on drawn variables; one with no Scala value (a quantifier over a whole type) is
"not checked", and `status` warns when nothing else checks it. `Checking.of(theory, id)` derives the lines `show`
prints (3.8); `Shown.of` says whether each piece of code is proven, tested or assumed.

### 2.8 Consistency

The statements must be proven non-contradictory: some meaning of every open value makes every claim and assumption
hold (owner §15, §18).

- **Groups** (`Consistency.of`): the bottom statements (stated, over every possible value, no parts) and the
  assumptions beside them, joined while they share an open value (a Declaration, or a Definition no proof or fixed
  value gives a meaning). Each group is `consistent_<i>`: for every value provided, some meaning of each open value
  makes each statement true. Statements above follow by proven steps, so consistency is carried upward. Each `always`
  about a store gets `start_<node>`.
- **Witnesses**, derived where possible, the group solved in substitution order: `∀ xs, s(xs) = e`, `e` mentioning
  nothing still open, gives `fun xs => e`; a bound gives the bound (one past a strict one); a witnessed value then
  stands for itself in the rest. Proven code is its own witness. `Equations.defining` reads the shape off the IR;
  `Defining` builds the term.

```scala
enum Witness:
  case Equation(symbol: SymbolName, from: NodeId, picked: Picked)
  case Bound(symbol: SymbolName, from: NodeId, picked: Picked)
  case Tested(symbol: SymbolName)
  case Missing(symbol: SymbolName)
```

- **In Lean** (`Whole.lean`), a witnessed group's theorem gives the witnesses in solving order, each earlier one
  substituted where a later one mentions it. Rooms' one group, `granted` open (`lean-spike/Dump.lean`):

```lean
@[frflow_defs] def consistent_0 : Prop :=
  ∃ (granted : RoomBookings → Booking → Prop), (Rooms.grantWhenNoOverlap.claim granted)
```

- **Status** (`GroupStatus`): `Proven` (Lean checked the witnesses), `Evidence` (only tested Scala stands for a value,
  `Witness.Tested`), `NotProven` (`Witness.Missing`). "Consistency not proven" is a status, not a failure: `status`
  warns, `show` says it, the mechanical review rule counts it unproven.
- **The contradiction search** (`unsat`, `clash`) is an early refuter only; consistency is never inferred from it.

### 2.9 Vacuity

Positive statements guard against a model that says nothing (rooms' `bookWhenFree` says a free room's request is
booked), and two small proofs more:

```scala
enum Vacuity:
  case Inhabited(statement: NodeId, ty: Ty)
  case Satisfiable(statement: NodeId, i: Int, over: List[Ty])
```

`inhabited_<node>`: some value of `T` meets an `always[T]`. `satisfiable_<i>_<node>`: each condition `A` of a claim's
`A implies B`, with what is bound above it (`Conditions`), can hold. The witness search (`testing.search.Witnesses`)
tries the generators' values first, then small values of each type (`Small`, SmallCheck-style), each judged by the
evaluator, deterministically, at most 5,000 candidates. A witness found goes to Lean (rooms: `(Booking.mk "" 0 1)`,
`(RoomBookings.mk [])`); a condition no candidate meets is "not shown". Examples may serve as witnesses but are never
required.

### 2.10 Examples as tests

Examples are ordinary tests beside the model, not part of any node (`RoomsExamples.scala`):

```scala
class GrantedExamples extends FrFlowExamples(rooms):
  example("back to back: granted"):
    granted(RoomBookings(List(Booking("Oak", 9, 10))), Booking("Oak", 10, 11)) is true

  example("overlapping: not granted"):
    granted(RoomBookings(List(Booking("Oak", 9, 11))), Booking("Oak", 10, 12)) is false
```

An example is a closed fact (`core.example.Example(name, givens, fact)`); `example(name, d := v)` sets provided
Definitions. Checked against the code (`ExampleRun`: `OnCode.Holds`, `Fails`, `NotEvaluated`, or `Abstract` for a fact
about Declarations) and against the claims in Lean (`example_<i>`, a try met by `frflow_example`); one that sets
values is shown "checked in Scala only". Nothing depends on examples: the theory and its Lean are the same without
them.

## 3. How a project reads: rooms end to end

Rooms books meeting rooms, in five files: `Rooms.scala` (the nodes, in the order they are named), `Book.scala` (the
store, its model, the program), `Calendar.scala`, `Knowledge.scala`, `RoomsExamples.scala`.

### 3.1 The domain and its words

```scala
final case class Booking(room: String, start: BigInt, end: BigInt) derives LeanType

/** A room's bookings, as the store gives them. */
final case class RoomBookings(bookings: List[Booking]) derives LeanType

val book = Definition[Booking => Program[Boolean]]("booking a request: whether it was booked")

// The root's words, over moments.
val covers = define { (b: Term[Booking], t: Term[BigInt]) => b.start <= t && t < b.end }
val apart = define { (a: Term[Booking], b: Term[Booking]) =>
  a.room =!= b.room || forall((t: Term[BigInt]) => !(covers(a, t) && covers(b, t))) }
val isFree = define { (held: Term[List[Booking]], request: Term[Booking]) => held.forall(b => apart(b, request)) }

// The calendar's words, over start and end times.
val noOverlap = define { (a: Term[Booking], b: Term[Booking]) =>
  a.room =!= b.room || a.end <= b.start || b.end <= a.start }
```

`granted` (2.2) is given its meaning by plain Scala, `book` by a proven program. A domain type derives its `LeanType`
once, where it is declared; a use without it says "Plain is not a domain type yet: add derives LeanType to its
declaration".

### 3.2 The store, its model, the program

```scala
trait Bookings[F[_], T[_]]:
  def inRoom(room: T[String]): F[T[RoomBookings]]
  def add(booking: T[Booking]): F[Unit]

object Bookings:
  given BoundaryOps[Bookings] = BookingsOps // what `derives BoundaryOps` will give

val store = Boundary[Bookings]("the SQLite table the bookings are kept in")

/** The store as the proofs see it: every booking, oldest first; a room's, as the store gives them. */
final class Stored[F[_]: Flow](state: Model[F, List[Booking]]) extends Bookings[F, Term]:
  def inRoom(room: Term[String]) = state.get.map(held => make[RoomBookings](held.filter(b => b.room === room)))
  def add(booking: Term[Booking]) = state.get.flatMap(held => state.set(held :+ booking))

val stored = store.model("every booking the store holds, oldest first")(Stored(_))

/** The program `book` is: the room's bookings read, the request added when granted, in one transaction. */
final class BookIfGranted[F[_]](store: Bookings[F, Term])(using f: Flow[F]):
  def run(request: Term[Booking]): F[Term[Boolean]] = f.atomically(
    f.flatMap(store.inRoom(request.room)) { held =>
      val booked = granted(held, request)
      f.as(f.cond(booked)(store.add(request), f.unit), booked) })

val bookIfGranted = program { (request: Term[Booking]) => BookIfGranted(store.recording).run(request) }
```

The model is written as a program is, an instance of the boundary's trait over the model's state (`Model[F, S]`:
`get`, `set`); `store.model(…)(Stored(_))` declares it with its instance, and `stored.in(world)` reads its state in
a world. Lean prints the boundary as a class, the model's operations as `do` blocks, `World`, and the instance on
`StateM World` (`planned/test/proof/resources/rooms/Boundaries.decls.lean`). The program's run on the models is
`bookIfGranted_run`.

### 3.3 The world outside, and what always holds

The five assumptions are those of 2.6; `endsAfterStart` and `neverOverlap` are in 2.3. The third rule is about what
the store gives:

```scala
val roomBookingsApart = Node.claim("A room's bookings, as the store gives them, never overlap.")(
  always[RoomBookings](r => r.bookings.pairwise(noOverlap)))
  .assuming(storeModel, neverOverlap)
```

The model's `inRoom` makes a `RoomBookings` and `granted` takes one, so the calendar's claims range over what the
store can give.

### 3.4 The roots: what booking does, and what it answers

```scala
val bookWhenFree = Node.claim("A request is booked exactly when its room is free.")(
  forall((request: Term[Booking], before: Term[World]) =>
    val held = stored.in(before)
    book(request).from(before) { (_, after) =>
      stored.in(after) === when(isFree(held, request))(held :+ request).otherwise(held) }))
  .assuming(storeModel, oneAtATime)

val answersWhetherBooked = Node.claim("Booking answers whether the request was booked.")(
  forall((request: Term[Booking], before: Term[World]) =>
    book(request).from(before) { (booked, after) => booked === (stored.in(after) =!= stored.in(before)) }))
  .assuming(storeModel, oneAtATime)
```

Each is one equation: overlaps are `neverOverlap`'s, and the Boolean answer is its own claim.
`when(c)(a).otherwise(b)` is Lean's `if`. Both read as runs of `book` and are proven of `bookIfGranted` by `impl`; a
run has no "nothing" to give, so neither gets an `idle` try.

### 3.5 The calendar

```scala
val grantWhenNoOverlap = Node.claim("A request is granted exactly when it overlaps no booked time.")(
  forall((held: Term[RoomBookings], request: Term[Booking]) =>
    granted(held, request) === held.bookings.forall(b => noOverlap(b, request))))
  .refines(grantWhenFree)
```

`grantWhenFree` (2.1) refines `bookWhenFree`; neither calendar claim writes a hypothesis, since `roomBookingsApart`
and `endsAfterStart` of each booking held are hypotheses on `held` in Lean. `granted` is the README's binary search
(`Calendar.scala`):

```scala
final class Calendar(held: RoomBookings):
  private val byRoom = held.bookings.groupBy(_.room).view.mapValues(_.sortBy(_.start).toVector).toMap

  def grants(request: Booking): Boolean =
    val room = byRoom.getOrElse(request.room, Vector.empty)
    val next = room.search(request)(using Ordering.by(_.start)).insertionPoint
    room.lift(next - 1).forall(_.end <= request.start) && room.lift(next).forall(_.start >= request.end)
```

It is correct as stated on what the store can give (`CalendarSuite`): on 500 generated cases meeting what always holds
(over 50 with two bookings of one room) it meets `grantWhenNoOverlap`; on a list the store cannot give (Oak 0–10 and
Oak 1–2, a request for 3–4) it is wrong, and that list breaks `roomBookingsApart`, so no case draws it; the
README's step-4 calendar, which forgets the booking after the request, is found by a generated case.

### 3.6 The knowledge base

```scala
val rooms = KnowledgeBase("Rooms")(bookWhenFree, answersWhetherBooked, neverOverlap, endsAfterStart,
  roomBookingsApart, grantWhenFree, grantWhenNoOverlap, storeModel, startsEmpty, onlyBookingWrites, oneAtATime,
  fromTheForm)
  .implementProven(book)(bookIfGranted)
  .implementTested(granted)(_ => (held, request) => Calendar(held).grants(request))
```

### 3.7 The store's adapter, tested and run

The SQLite store is tested against the model, not trusted (`StoreModelSuite`, with an in-memory stand-in):

```scala
  private def checked(byRoom: Boolean = true, adds: Boolean = true) = stored.checkedAgainst(
    start = held => Ref[IO].of(held).map(Memory(_, byRoom, adds)),
    observe = memory => memory.bookings)
```

`start` makes the implementation holding a model state; `observe` reads its state back. `ModelTests.run` runs
generated calls (`Runs`, values meeting each `always[T]`) on both and reports the first answer that differs
(`Difference.Answer`) or a final state that does (`Difference.State`). On 200 runs the stand-in agrees; one that
forgets the room filter is found at `inRoom`, one that forgets to add by its state. The suite also runs
`BookIfGranted` in `IO` over `eval.Running` on the store lifted (`BookingsOps.lifted`), as production does: a free
request is booked, a clash is not.

### 3.8 What check and show say

`show` prints how each statement is checked, every line derived (from `CheckingSuite`, which pins them; some nodes'
lines elided):

```text
bookWhenFree          proven of book's program, bookIfGranted
                      assumed by the code calling book
                      rests on the store behaving as stored: storeModel
                      rests on one run at a time on stored: oneAtATime
grantWhenNoOverlap    tested against granted's Scala on generated cases
                      assumed by the code calling granted
                      consistent with grantWhenNoOverlap: witnessed, for Lean to check
grantWhenFree         proven from its parts (grantWhenNoOverlap)
                      not checked against granted's Scala: the statement has no Scala value (it quantifies over
                      every value)
oneAtATime            the world outside: runs on stored never interleave
```

Lean is asked `complete` of `grantWhenFree` (not of the root) and, as `lean-spike/Dump.lean` states and `Proofs.lean`
proves them: `impl` of both roots; `cover_book` and `made_inRoom` of the rules; `consistent_0`; two `start_` (by
`frflow_auto`); two `inhabited_`; `example_0` to `example_2`. The root's `impl`:

```lean
/-- Every result of bookIfGranted_run meets bookWhenFree, given what grantWhenFree promise. -/
@[frflow_defs] def impl : Prop :=
  ∀ (granted : RoomBookings → Booking → Prop), ∀ (h_grantWhenFree : (Rooms.grantWhenFree.claim granted)), (Rooms.bookWhenFree.claim (Rooms.bookIfGranted_run granted))
```

The store's model is not a hypothesis: it is inside `bookIfGranted_run`. A program's Boolean result is Lean's `Prop`
(`Booking → World → (Prop × World)`), decided by Lean's classical `if`. The proofs of `impl` and `cover_book` are
written by hand: the run's equation, then cases on the answer.

### 3.9 Auth: a purpose over Declarations

```scala
val accessExactly = Node.claim("A user reaches a path exactly when they are signed in and authorized for it.")(
  forall((u: Term[UserId], p: Term[Path]) => access(u, p) === (signedIn(u) && authorized(u, p))))

val grants = Definition[List[Grant]]("the grant table as stored when a request is decided")

val grantsAuthorize = Node.claim("A user is authorized for a path exactly when a grant names them and the path.")(
  forall((u: Term[UserId], p: Term[Path]) => authorized(u, p) === grants.exists(g => g === make[Grant](u, p))))
  .refines(accessExactly)
```

`sessionsSignIn` and `requestsReach` refine `accessExactly` alike; `grants` and `sessions` are provided. Each
Declaration's group is witnessed by the equation refining it, for every table provided; placed at the bottom together,
the three are solved in substitution order; with nothing tying them to the domain, "consistency not proven".
`AuthExamples` sets `grants := …`: "checked in Scala only".

## 4. The compiler

### 4.1 Phases and their types

| Phase | From → to | Where | Effects |
|---|---|---|---|
| construct | the user's vals → `Node`, `Term`, values, `KnowledgeBase` | `dsl` | none |
| elaborate | `KnowledgeBase` → `ValidatedNec[ElabError, Elaborated]` | `dsl.kb.Elaborate` | runs each lambda once |
| validate | `Elaborated` → `ValidatedNec[Problem, Valid]` | `core.analysis.Validate` | pure |
| resolve | `Valid` → `Resolved` | `core.analysis.Resolve` | pure |
| run Scala | `Resolved`, examples → `Computed` | `project.program.RunScala` | `F: Sync` |
| obligations | `Resolved`, witnesses → `NodeObligations`, the whole theory's | `proof.obligation`, `proof.whole` | pure |
| lower, lay out | obligations, `TermTable` → `List[LeanModule]` | `proof.lean`, `proof.layout` | pure |
| print | `LeanModule` → `String` | `proof.lean.print.Print` | pure |
| prove | modules → `Judged` → `NodeCheck` | `project.program.NodeChecker` | `F` (`Lake`) |
| test | `Theory`, `Semantics`, `Plan`, `Draw` → `TestReport` | `testing` | pure given a seed |
| project | `Resolved`, checks, tests → `Content`, `Subjects` | `project.pipeline` | pure |
| review | `Subjects`, `Ledger` → `Map[NodeId, Standing]` | `decision.review.Standings` | pure |
| decide | `Reading`, `Command`, `Authorship`, `Deciders` → `Either[Refusal, Ledger]` | `decision.rules.Decide` | pure |
| export | `Analysis` → snapshot, checks, tests, ledger | `wire` | codecs |
| view | `Analysis`, warnings → `View` | `api.view` | pure |

Elaboration keeps each term with its IR (`Written`) and reads each recorded program in its own `State`. `Valid` is an
opaque type only `Validate` makes. `Analysis(valid, inputs, computed)` holds the later stages as lazy values, so an
operation computes only what it reads, each stage once.

### 4.2 Terms in tagless-final style

Terms follow Kiselyov's course (owner §5; "Typed Tagless Final Interpreters", LNCS 7470, cited as §n; Carette,
Kiselyov, Shan, JFP 2009, CKS). **The language is its algebras** (§2.1, §3.2): fifteen over a representation `T[_]`,
bundled by `Sym`; a term is a polymorphic function, the same value for every interpreter:

```scala
trait Sym[T[_]] extends Logic[T], Equality[T], Arith[T], Constants[T], Lists[T], Options[T], Eithers[T],
    Quantifiers[T], Records[T], Sums[T], Functions[T], Named[T], Variables[T], Worlds[T], Annotations[T]:
  def extension[E[_[_]]](key: Ext[E]): Option[E[T]] = None
```

```scala
type Final[A] = [T[_]] => Sym[T] => T[A]
```

The algebras: `Logic`, `Equality`, `Arith`, `Constants`, `Lists` (with `foldLeft`, `pairwise`, `nodup`), `Options`,
`Eithers`, `Quantifiers` (`forall`, `exists`, `always`), `Records`, `Sums` (an eliminator, one `When` per case),
`Functions` (`lam`, `app`, `let`), `Named` (`param`, `define`), `Variables`, `Annotations` (`noted`) and `Worlds` (a
model's state, a program's `runs` and `fails`, `outside`). Object types are host types (`T[Boolean]`,
`T[List[Booking]]`), so no interpreter tags a value. **Interpreters** (§3.2), one printer and one evaluator:

| Interpreter | Representation | Used for |
|---|---|---|
| `proof.lean.term.LeanTerm` | `Scope => LExpr` | every term's Lean, the only printer |
| `eval.term.Evaluate` | `Env => Either[EvalError, A]` | every term's Scala value, the only evaluator |
| `core.term.interpret.ToExpr` | `Int => Expr` | the IR, for the analyses only |
| `Collect` | `List[Annotation]` | what a term declares, and faults |
| `Hypotheses[T]` | `Split[T, A]` | `h1 implies (h2 implies c)` as Lean's `intro` |
| `PartialEval[T]` | `Known[T, A]` | simplification before printing (CKS §4) |
| `Opened[T]` | `Opening => T[A]` | a claim read as a call, as its post |
| `Guarded[T]` | a transformer of `forall`, `exists` | each `always[T]` as a hypothesis |
| `Forward[T, U]` | a transformer's base | forwarding what a transformer leaves alone |

`Defining` and `Conditions` (in `core.consistency`) are transformers too. There is no duplicating interpreter and no
typechecker: both exist for terms read from text (§2.3), and FrFlow's never are.

**Binders are host functions** (HOAS, §3.2). The evaluator applies one to the value, `ToExpr` to the variable at its
depth (`VarId.level`), and `LeanTerm` names it by the developer's name, or with the first free number when that is
taken (`x_1`). Nothing is numbered before an interpreter binds it.

**The user's `Term[A]` is closed and concrete**: it holds `run: Final[A]` and nothing else; `b.start` is `Selectable`
over derived selectors; `==` on terms does not compile, saying to write `===`; `T[_]` appears neither in user code nor
in error messages. The price is one cast, since a body is the user's `Term[A] => Term[Boolean]` but an interpreter
applies it to its own `T[A]` (`dsl/frflow/dsl/term/Term.scala`):

```scala
  def bound[T[_], A](owner: Sym[T], x: T[A])(using LeanType[A]): Term[A] =
    Term([U[_]] => (s: Sym[U]) => if s eq owner then x.asInstanceOf[U[A]] else outside)
```

Run by any other interpreter, the variable fails at once ("FrFlow bug: a bound variable used outside its binder",
tested).

**The hard constructs are algebra operations** in all three interpreters (`Changes.scala`): a sum's eliminator,
`c.on[Change.Book](b => …).on(Change.Clear)(…)`, each arm's type test written by `CaseMacros` (no cast), printed
as a `match`; records made (`make[Booking](room, t, t + 1)`) and copied (`b.updated(_.start, t)`); the folds and
`let`; `allDistinct`, `pairwise` and `forall` of a define; a program's runs. A define is one `term.Body` (name,
curried type, a `lam` per input) applied one argument at a time, so `param`, `define`, `lam` and `app` cover every
arity.

**Notes are an interpretation**: what a term declares, and faults, are on the term (`noted`), gathered once by
`Collect` into a monoid (`Declarations`); there is no registry. A project's own operation is a define, or an algebra
outside the core found by a typed key (`Count` in the tests, via `Sym.extension`, falling back to its meaning in the
core).

**What is not compositional** (§2.4, §3.3) reads the initial form (the "what changed" view, the refutation's hint,
the layout, `CallForms`, where a witness sits) or passes context (`LeanTerm`'s scope, `Opened`, `Guarded`,
`Hypotheses`, `PartialEval`, which folds what is known: `1 < 2 && p` is `p`). The code fingerprint hashes source, not
terms.

**Syntax and laws.** `implies` is alphanumeric, so it binds last; a macro refuses `a implies b implies c` without
parentheses. On 300 generated terms (`TermLawsSuite`): a written lambda gives the evaluator's value, folding keeps
values, the IR is typed as the term; the printer's text reads back and prints the same (`PrinterLawsSuite`). With
`lake` in the suite (step 3), Lean will decide each generated term as the evaluator does.

### 4.3 The IR

`core.expr.Expr`, made only by `ToExpr`, is a simply typed lambda calculus with data, containers and quantifiers;
every node carries what its type needs (`Exprs.typeOf` is total). A binder's id is its level; a recorded step is
numbered negative, apart from every level (`VarId`). One operator per meaning (`Contains` of a list, option or set is
one `PrimOp`); every operation with a body is `Expr.Iterate`. `Mentions`, a monoid, says what an expression mentions.
`Prog[E]` is a program's steps, first order, generic in what a step holds (`Prog[Stated[?]]` for back ends,
`Prog[Expr]` for analyses): a free monad over boundary operations and model state, with errors, loops and concurrent
steps (`Par`, `ParEach`, `Race`, `Guard`, `Atomic`). `Written(value, source, form)` keeps the term or steps (what back
ends read), their IR (what analyses read) and the Scala as written (what the developer decides); only its three makers
build it, so `value` is always `form`'s IR. The IR is never printed or run.

### 4.4 Programs over boundaries

A boundary is the developer's trait over an effect and a value form (`Bookings[F[_], T[_]]`); in programs and models
`T` is `Term`. A program is a class over its effect asking only for `Flow[F]` (`dsl/frflow/dsl/flow/Flow.scala`,
excerpt):

```scala
trait Flow[F[_]] extends Monad[F]:
  /** One of two programs by a condition at hand. */
  def cond[A](c: Term[Boolean])(ifTrue: => F[A], ifFalse: => F[A]): F[A]
  def each[X: LeanType](xs: Term[List[X]])(body: Term[X] => F[Unit]): F[Unit]
  def raise[E, A](error: Term[E]): F[A]
  def handle[E: LeanType, A](fa: F[A])(handler: Term[E] => F[A]): F[A]
```

`Flow.scala` also has `guarantee`, `race`, `parTupled` and `atomically`, and `ifM`, `bracket` and `timeout` made of
them; `RecordingSuite` records each as the step Lean reads (with `each`, `raise` and `handle`). Every combinator is
kept (owner §2) and given a use in an example. `collect`, `fold`, `parCollect` and `attempt` (today's `traverse`,
`foldM`, `parTraverse`, `attempt`) are not in the planned code: step 2 adds them, each with a `RecordingSuite` test.
`F` has three interpreters:

- **Lean's**: `Recording`, a pure `Flow[Recorded]`, with the boundary's recording instance (`store.recording`).
  `program { … }` reads the recording into `Prog[Stated[?]]` (`ReadRecording`, steps numbered in its own `State`);
  Lean prints a `do` block over `[Monad m] [Bookings m]`, run on the models' instance on `StateM World`. A bound term
  is shared as Lean's `let`.
- **Production's**: `eval.Running` for any `F: Async`, reached through `knowledge.running[F](bindings*)`: a condition
  evaluated by `Evaluate`, `atomically` under one `Mutex`. The adapter is plain Scala over plain values
  (`Bookings[IO, Id]`), lifted into `Bookings[IO, Term]` by `BoundaryOps.lifted`, which evaluates each argument, calls
  the adapter and makes the result a term again. Nothing is checked.
- **Scala tests'**: the recorded `Prog` run by `eval.flow.FlowInterpreter` against a `World`: the models (examples,
  model tests) or the adapters (interleavings).

`BoundaryOps[B]`, which `derives BoundaryOps` will write (rooms writes it by hand), gives the class Lean declares,
`recording`, `call`, `model` and `lifted`. `LowerModels` prints boundaries, models, `World` and each program's run on
them (`f_run`). Step 4 adds the law that a program's recording run on the models gives what `Running` gives on the
models' instances; no suite states it yet.

### 4.5 The front end: nodes, names, errors

A DSL node is `Node(head: Head, statement: Deferred[Statement])`: the head as written (id, sentence, position, links),
the statement built when elaborated. `Source.valName`, read at compile time, names nodes, values, types, boundaries
and models: one name in code, reports and Lean. Today's `Node` fields each have a place: `why` is the decision's
reason, parents are edges, `post` and `op` are derived from the formula, `file` and `at` are a
`Sited(node, at: Span)`; `kept`, `runCheck`, `ideaSection` and `enforce` are gone.

**An error waiting for its place.** A part built later is a `Deferred[A]` (an `Applicative`: errors accumulate,
declarations merge). An error found before its place is known is a `Fault`, carried in a term's notes or thrown as
`Failure(fault)`, and placed once as `ElabError(at: Site, fault: Fault)`.

### 4.6 Validation and resolution

`Validate(e: Elaborated): ValidatedNec[Problem, Valid]` returns every problem at once, one `Problem` case per thing
wrong: the graph (`DuplicateId`, `NoRoot`, `AboveItself`, `ParentOutside`, `DesignWithoutParent`, `UnderDesign`,
`PremiseNotAssumed`, `OutsideAsPart`, `OutsideClaimed`); the world outside (`PremiseMissing`, `PremiseNotNeeded`,
`WriterNotListed`); the vocabulary (`ReservedName`, `DeclaredTwice`, `CodeOnlyInStatement`); values (`Undefined`,
`DeclarationInCode`, `CodeWithoutClaim`, `PartNotCalled`).

`Resolve(v: Valid): Resolved` computes once what each node uses, calls and rests on (`Callees`, `reliesOn`). `Scope`
derives where an `always` applies: the Definitions and store programs whose values can hold a `T` (read off `Ty`), its
makers, and the programs writing a store. Nothing is exempt: a claim mentions only what it constrains.

### 4.7 Obligations derived from formulas

An obligation is a proposition in the logic of refinement before any Lean syntax (`proof.obligation.Prop`): claims
applied to their open terms, `Implies` with named hypotheses, `Iff`, `Both`, `Not`, `Forall`/`Exists` over open terms,
`ForEvery`/`ForSome` over named symbols, `Keeps`, `Makes`, `Starts`, `Inhabited`, `Commutes`. A formula is held as
written (`Prop.Formula(Written[Expr])`); `TermTable`, computed once, says what each declaration is applied to.

```scala
enum ObligationName:
  case Complete, Feasible, Impl, RootImpl
  case Cover(op: String)
  case Made(maker: String)
  case Tried(kind: TryKind)
  case Commute(i: Int)
  case Consistent(group: Int)
  case Start(node: NodeId)
  case Inhabited(node: NodeId)
  case Satisfiable(node: NodeId, i: Int)
  case Example(i: Int)
```

Of a node: `complete`, `impl`, `feasible`, `cover_<op>`, `made_<maker>`, `commute_i` (for `parTupled`, `parCollect`).
Tries, within a budget and one-sided (proven, they show something wrong): `needed_C`, `vacuous`, `restates`,
`restates_i_C`, `clash`, `unsat`, `idle`. A failed step is refuted when a node's one part fixes its result:
`StepRefutation` finds a case where the claim fails with that answer, and `RefutesModule` proves it. Of the whole
theory (`proof.whole`): `consistent_<i>`, `start_<node>`, `inhabited_<node>`, `satisfiable_<i>_<node>`, `example_<i>`.
Each obligation carries the sentence its Lean is documented with.

### 4.8 The Lean back end

The Lean AST (`proof.lean.ast`) says everything FrFlow generates; `LExpr` has no raw-text case. `LeanTerm` prints
every term, a define's body once as its `def`. Lowering gives only the structure around terms its Lean, handing each
term to `Printed`: `LowerProg` (a `do` block, names in `State[Naming, _]`), `LowerProp` (a `Writer` of open terms
met), `LowerObligation`, `LowerValue`, `LowerModels`, `LowerKeeps` (what `cover_` and `made_` declare),
`LowerWitness`. `Print` is a fold that decides nothing. `LeanProject` lays out node, root, vocabulary, whole-theory
and refutation modules. `proof.reading` and `proof.verdict` hold today's proof-file rules one case each, Lean's output
and the judges. The Lean library gains `frflow_witness` and `frflow_example` (14 lines).

`CrmModulesSuite` prints four of crm's files byte for byte (`Boundaries.lean`, `Def_expireOnce.lean`,
`Def_expireOnce_run.lean`, `ExpiryJob/Spec.lean`); rooms' four golden files are in `lean-spike/Dump.lean` verbatim and
compile. Today's Lean is a reference, not a constraint (owner §2, D).

### 4.9 Testing before production

Property-based testing stays in full and carries every check the running service made:

- **Plain code against every claim mentioning its Definition** (`PropertyTests`): inputs drawn, the values the code
  reads made by `eval.run.Wiring`, the call judged by `CallCheck` (the post, and each `always[T]` of the call's
  values, `Made`) or the claim evaluated whole; the first failure shrunk, saved, replayed first; a claim's parts'
  coverage.
- **`Wiring`** makes a call's values explicitly (defines, the meanings of what it calls, the values given), for
  examples, tests and production's `knowledge.code(d)(bindings*)` alike.
- **An adapter** against its assumption's formula and its model (`ModelTests`, 3.7).
- **Interleavings** of a concurrent program on the adapters, over the recorded `Prog` Lean proves, deterministic under
  `TestControl`; production's concurrency on its own (`RunningSuite`).
- **The step refutation** and **the witness search** (`testing.search`).

Every value drawn by its type meets each `always[T]` of the type (`Respecting`). A run is a function of its seed and
the code.

### 4.10 Views and the API

`View(nodes, roots, whole, overview, warnings)` is derived once (`Views.of`); front ends never see `Analysis`.
`WholeView` holds the consistency groups, what is shown possible, and the examples.
`NodeView(id, says, place, proof, code, review)` has one group per concept (`Says` holds the formula, `checking` and
the decision's reason); `Overview` is `Tally[K]` fields, a commutative monoid. The API is three algebras in
`FrFlowApi[F]`:

| Algebra | Operations |
|---|---|
| `Reading` | `view`, `diff(node)`, `find(words)`, `modelFingerprint` |
| `Deciding` | `developer(as)`, `preview(command, by)`, `decide(command, by)` |
| `Proving` | `render`, `status`, `check(only): Stream[F, CheckEvent]`, `ci`, `scaffold(node)` |

## 5. Modules and dependencies

```text
   core ◄── dsl ◄── eval ◄── testing        (facade `frflow.*` in eval: the DSL, programs, env(d), d.fn, code)
    ▲  ▲
    │  └── proof
    └───── decision
   wire ─► proof, decision, testing          (the export formats)
   project ─► proof, testing, decision, wire (the shell: algebras, programs, the analysis)
   api ─► project ;  cli, web ─► api ;  agent ─► cli, web
```

| Module | Depends on | Holds |
|---|---|---|
| `core` | cats-core | names, `Ty`, term algebras, `Expr`, `Prog`, statements, analyses, checking, consistency |
| `dsl` | core | the user's syntax, elaboration, `Term[A]`, `Flow`, `Boundary`, models, macros |
| `proof` | core | obligations, the Lean AST, the term printer, lowering, layout, judges |
| `eval` | dsl, cats-effect-kernel, -std | the term evaluator, `Running`, `CallCheck`, `Wiring`, `ExampleRun`, `FlowInterpreter` |
| `testing` | eval, cats-effect | `Draw`, `Respecting`, `PropertyTests`, `ModelTests`, `Interleavings`, searches |
| `decision` | core (names, `graph.Walk`) | content, ledger, deciders, payload, review, rules |
| `wire` | proof, decision, testing, circe | the snapshot by kind; codecs of ledger, deciders, checks, tests |
| `project` | proof, testing, decision, wire, cats-effect, fs2 | algebras, programs, `Analysis`, contents, fingerprints |
| `api` | project | `Reading`, `Deciding`, `Proving`, `FrFlowApi`, views |
| `cli`, `web`, `agent` | api (agent also cli, web) | front ends and the agent layer |

Each module has its own top package (`frflow.core`, …), so `private[core]` is a real boundary. The planned code has
the first nine; `cli`, `web` and `agent` keep their structure and are rebuilt on the new API. Serialization points
outward: only the shell depends on `wire`. Front ends see `api.view` and `api.node` values only. Production code
depends on `eval` (and through it `dsl`, `core`) and never on Lean, the ledger, the tests or the CLI.

Planned so far (files / lines): `core` 145 / 3,072, `dsl` 69 / 2,182, `proof` 79 / 2,058, `eval` 26 / 719, `testing`
22 / 428, `decision` 42 / 694, `wire` 14 / 184, `project` 25 / 622, `api` 27 / 381. With the ports written and `cli`,
`web` and `agent` rebuilt, the projection is about 13,700 lines in about 570 files, against today's 12,008 in 347:
about 12% more, consistency and vacuity among it, in smaller files, with no type over six fields.

## 6. Data: decisions, deciders, ledgers, fingerprints

**Content.** `Content(fields: List[(String, FieldValue)])` is a node as the developer decides it: named fields in a
fixed order, a canonical print, `hash` (whitespace runs ignored) and `ref` (the exact form a signature covers). One
form (`Contents.of`): `kind`, `parents`, `parts`, `assumes`, `statement`, `formula`, `vocabulary`, `checking`,
`governs`, `call`, `replaces`, `reliance`, `failure`, `implementation`, `model`, `implementations`. No `why`, source
excerpt or `idea`. `Meaning.own` (cause `self`) leaves out `parts` and `parents`, but a design keeps its `parents`.

**Ledger and review.** The `Ledger` is append-only; review states are a fold of it over the current graph, parents
first (`Standings`). A node returns for a cause: `self`, `above` (unless only words moved, `Reworded.only`), `parts`,
`code`, `revisit`, `merged`, a parent rejected; `Cause.movedUnderCode` lets the CLI say a failing case as the claim's
change. Rules see a `Subject`, never the IR or Lean; `Decide` refuses a reason under three words, then applies one
rule class per `Command`. Ledgers start fresh (owner §2, G).

**The mechanical rule.** A decision is mechanical when the developer can take it in a batch: `Mechanical.why` gives
today's chain, in its order, of why one is not (it holds a choice; it is not under review; a cause other than `self`,
`above` or `parts` moved it; its meaning moved; its new parts are not proven to make it; it is not proven again; it
waits for a node the batch does not accept first). "Not proven again" reads the checks through `ProofStanding`, made
by `ReadProof` as today's `Proofs.unproven`, one `Unproven` case per line, with `Unproven.Consistency` added.
`Reading.notMechanical` folds this parents first, and `confirm` accepts every node it finds mechanical. Once a rule
has added decisions, `Seals.signAdded(before, after, sign)` signs those `after` has and `before` did not.

**Who may decide.** `.frflow/deciders` is committed (`decision/frflow/decision/ledger/Deciders.scala`):

```scala
final case class Deciders(entries: List[Decider], after: Option[String], seal: Seal):
  def allows(name: String, key: String): Boolean = entries.exists(d => d.name == name && d.key == key)
```

The first version is signed by its first entry, each later one by a key the version before listed, naming that version
(`after`), so replaying an old list breaks the chain and cannot restore a removed decider. FrFlow reads only committed
versions (`Git`) and takes the last when each follows the one before. A decision counts only when its key is listed
under its decider's name and the signature verifies; `DecideProgram` refuses an unlisted key before any rule
(`Refusal.NotADecider`). `init` writes the first list. `Payload.of(id, d)` joins with NUL the node id, action, by, at,
reason, rejected, chain, code fingerprint, commit, after and `content.ref`.

**Fingerprints.** `CodeFingerprints.of(files)` hashes a design's governed files, sorted, as the simple lexer reads
them (owner §2, F): comments blanked, blank lines and trailing spaces dropped, indentation kept, runs of spaces
collapsed. A change of meaning always moves it; comment and spacing edits do not; a few harmless edits do (`f(/*a*/x)`
to `f(x)`).

**Exports.** The snapshot (`.frflow/kb.json`) is `wire`'s own rows by kind, made by one mapping (`Rows`), printed by
`--json` and read by no FrFlow module; `wire` also has the codecs of the ledger, deciders, `checks.json` and
`tests.json`.

## 7. Errors and effects

### 7.1 Errors

| Where | Type | Channel |
|---|---|---|
| elaboration | `ElabError(at: Site, fault: Fault)` | `ValidatedNec`, all collected |
| structure | `analysis.Problem` | `ValidatedNec`, all collected |
| either, at the shell | `Problems.NotElaborated`, `Invalid` | raised in `F` (`NoStackTrace`) |
| evaluation | `EvalError` (`Quantified`, `Unbound`, `NoDefine`, `NoCase`, …) | `Either` |
| a program run in Scala | `FlowError` (`NotEvaluated`, `NoModel`, `NoOperation`) | raised in `F` |
| decisions | `Refusal`, e.g. `NotADecider(name)` | `Either`; the caller goes on |
| a check | `Finding` cases in `Judged`, `NodeCheck` | data |
| the theory as a whole | "consistency not proven", "not shown", "not checked" | data: a status |
| tests | `TestReport`, `Failure(inputs, broke: Broken, …)`, `Difference` | data |
| plain code, a running program | `NotEvaluated(EvalError)` | thrown |
| the shell (no Lean, unknown node) | `FrFlowError` | raised in `F` |
| FrFlow bugs | `IllegalStateException`, "FrFlow bug" | where types rule the case out |

`Fault` has thirteen cases (`NoType`, `NotData`, `NoField`, `NotAClaim`, `ProgramMentioned`, `MeantWhereWritten`,
…). `Broken.Always` is an `always[T]` a call's value breaks. Production code has no `Either` to return, so plain
code evaluating a term with no Scala value throws `NotEvaluated`; inside the evaluator `app` turns it back into
`Left`. Text for the developer is made only in `cli` and `web`.

### 7.2 Effects: where F[_] is used, and why

`core`, `proof`, `decision`, `Evaluate` and the generators have no effect type; `dsl` has `Flow[F[_]]` but runs
nothing. Each `F[_]` pays for itself:

| Algebra or program | Why over `F[_]` | Second interpreter or law |
|---|---|---|
| `ProjectFiles[F]` | the checker tested without a disk | in memory; a read after a write gives it |
| `Lake[F]` (`Resource`) | planning and judges tested without Lean | scripted, answering by module |
| `Git[F]` | decision tests without a repository | in memory |
| `LedgerStore[F]` (`Resource`, the lock) | the CLI and web view may decide at once | in memory; stores only on `Right`, serialized |
| `KeyRing[F]` | tests never touch the developer's key | a key in memory; deciders read from `Git` |
| `ReadInputs`, `RunScala`, `CheckProgram`, `NodeChecker`, `DecideProgram` | programs | ask only `Monad`, `Parallel`, `Clock` |
| `FrFlowApi[F]` | the CLI, web and agent suites | in memory; `preview` shows what `decide` records |
| `Flow[F]` | a program read by Lean, run in production | `Recording`, `Running`; agree on the models |

Concrete `IO` appears only in the web server, the CLI's `main` and the terminal; in production the developer picks
`F`.

### 7.3 State and casts

State, each piece named: `KnowledgeBase.elaborated` (a `lazy val`), `Running`'s lock, and a recording's reading's
`State`. Atomics and locks are allowed only in `eval.Running` and `FlowInterpreter.concurrent`, `ThreadLocal` nowhere.
Casts are in thirteen named places (`Guards`, `Keeping`, `Making`, `Definition.called`, `Term.bound`, `eval.Fn`,
`ReadRecording`, `Running.handle`, `ValuesSyntax.apply`, `Defining`, `Conditions`, `AtValue`, `Written.term`), each
typed by what was read before it. No interpreter of terms casts but `Evaluate`, through `Fn.as`, where it reads
untyped given values; no unchecked type test is left outside `Fn`.

## 8. What is removed from today's library, and why

`features.md` is the full table, feature by feature.

**Run-time checking** ("FrFlow is for testing before production and strict static guarantees", owner §2). Removed:
the `runtime` module (service wiring, `Guard`, the assumption watch, sampling, the reporter, `ContractViolation`),
`.checkedBy` and its `check` obligation, `.checkedAtRunTime`, `kb.reporting`. `knowledge.code(d)(bindings*)` is
`service`'s wiring returning the plain function, so servers lose their `ContractViolation` branches. Where each check
went:

- a contract's result, the rules it keeps: `PropertyTests` (every claim, each `always[T]` of the call's values) and
  the examples, the same judgement (`CallCheck`) before production;
- an outside system's adapter (crm's `recordsByQuery`, keycloak's `sessionLookup`): `PropertyTests` against its
  assumption, examples, `ModelTests`; crm's seeded SQL bug is caught by `check`, but a bug only real data shows is no
  longer caught when it happens;
- facts about a service's values (sharing's `HousekeepingOnTime`): checked under examples' and tests' values only,
  otherwise trusted;
- `checkedBy`'s cheaper check: gone; tests check the post itself.

What production trusts is what it trusted already: the accepted assumptions, the translation to Lean, and the inputs
the tests reach.

**Kinds and forms beside the owner's concepts**, said now with the three kinds of node:

| Today's | Now |
|---|---|
| contract on an operation | a claim on a Definition, read as a call (2.7) |
| invariant of a type / of a store | a claim of `always[T](x => …)` / `always(stored)(s => …)` |
| a store's model | an assumption, `store.behavesAs(stored)` |
| definition node (`authorized := …`) | a claim of one equation, or a `define` |
| `Param`, `Operation`, `Open` | `Declaration`, `Definition` |
| `.expects(statement)(consequence)` | a claim the expecting claim refines |
| `.failsChangingNothing[E]`, `.onFailure` on a node | part of the run in the formula |
| `.keeps`, `.exempt`; relations of answers | derived (`Scope`); a claim over the Definitions it relates |
| `.examples`, `allows`/`forbids`, `bind`, `eval_i`/`probe_j` | examples as tests (2.10) |
| two definitions of one term | two claims, one `.replaces` the other |
| `==>`, the Boolean `fold`, `before(stored)` | `implies`, `when(…)(…).otherwise(…)`, `stored.in(before)` |

**Everything else**: `why` on nodes (the examples' `why` texts are offered as the reasons of their first decisions);
`IDEA.md`, idea sections and numbered questions (owner §1: the purpose is stated by the root statements; a README is
prose FrFlow does not track); ambient state (`Param.value`, `Bindings`, `Watch`, `Building`, the `LeanType.known`
registry, the fresh-variable counter, reflection on lambdas and bytecode; the examples' 34 `p.value` become `env(d)`);
today's `Flow` values and `Flow.effect`; content forms, `confirm --rebind`, `Retired` ids, text fingerprints and filed
keys as authority; the compiled-define memo.

## 9. The rebuild plan

The new FrFlow is built beside today's in this repository and replaces it once every example runs on it. Today's
modules are not changed, but for step 0, which records their outputs.

**Layout.** New modules live under `next/<module>/` (sbt ids `next-core`, …) with their own top packages, so old and
new never share a classpath: no new module depends on an old one, and a ported example on new ones only. Step 14 moves
`next/*` to `modules/*`.

**Equivalence.** Step 0 records today's outputs under `reference/`. Each ported example's `PortSuite` checks that (1)
every node proven in the reference is proven, and each is proven, tested or assumed as there, differences listed and
judged; (2) each seeded bug is caught; (3) examples and property and model tests pass with the reference's seeds; (4)
no statement is weakened: a generated `example : Old.claim ↔ New.claim` per node, proven by `simp [frflow_defs]` or
listed. `WalkthroughSuite` replays the README's rooms changes (steps 4–6) on a copy and compares `check` and
`review` output line by line: the failing case (Oak 0–4, a request 0–1), the step refuted by a case Lean proves
(Elm 2–4, a request 0–2), the claim back for review.

**Steps**, each one reviewable change, green on `sbt test` (old and new) and `sbt leanTest`:

| Step | Delivers | Checked by |
|---|---|---|
| 0 | `ReferenceCapture`: today's Lean, standings, CLI text, walk-through, seeded bugs | the capture; FrFlow unchanged |
| 1 | `next/core`: term algebras and core interpreters, IR, statements, validation, checking, consistency | `typeOf`, `Mentions` laws, every `Problem` by name |
| 2 | `next/dsl`: `Term[A]`, macros, the user's forms, `Flow`, boundaries, models | `RecordingSuite`, `FormsSuite`, claims suites, ported suites |
| 3 | `next/proof`: `Prop`, Lean AST, `LeanTerm`, lowering, layout, judges, tactics | `PrinterLawsSuite`, `CrmModulesSuite`, a test per try and rule |
| 4 | `next/eval`: `Evaluate`, `Running`, `CallCheck`, `Wiring`, `FlowInterpreter` | `TermLawsSuite`, `RunningSuite`, recording agrees with running |
| 5 | `next/testing`: generators, `PropertyTests`, `ModelTests`, searches, examples' runner | ported suites with seeds, `Gen` laws, `SmallSuite` |
| 6 | `next/decision`: content, ledger, `Deciders`, review, rules | ported decide and standing suites, `DecidersSuite` |
| 7 | `next/wire`: rows and codecs | a round trip per file |
| 8 | `next/project`: algebras with in-memory interpreters, programs, `Analysis` | `check`'s suites over the in-memory interpreters |
| 9 | `next/api`: the three algebras, views, `FrFlowApi.inMemory` | `api`'s suites |
| 10 | `next/cli`, `next/web`, `next/agent`; `init` writes the deciders' list | `cli`'s and `agent`'s suites, a web smoke test |
| 11 | rooms ported as section 3 writes it; the README walk-through rewritten | rooms' suites, the Lean spike, `PortSuite`, `WalkthroughSuite` |
| 12 | auth, then keycloak, then crm ported | each `PortSuite` and its seeded bugs |
| 13 | sharing ported, with the kept combinators' uses | its `PortSuite`, fault sweep and interleavings |
| 14 | today's modules deleted, `next/*` moved, docs and skills rewritten | the architecture test at target, size baseline at zero |
| 15 | the owner decides each example's ledger with his key | `confirm` for the mechanical nodes; nothing earlier counts |

Step 2 also writes every node of the five examples in the three kinds before any port, and keeps the compile-time
spike in the build. Step 5 makes drawn values meet their fields' rules (10.2). In step 12, auth's `Param`s become
Declarations and Definitions (`grants`, `sessions` provided, `admit` tested) and `Server` calls
`knowledge.code(admit)(…)`; keycloak loses its `checkedBy`; crm's `Database[F, T]` becomes tagless, its expiry job
gains its `ifM`, and `noCrossTenantRead` becomes a root over two Definitions. In step 13, sharing uses `timeout`,
`race`, `bracket` and `parTupled`, each under a proven claim. Step 14 rewrites `docs/USAGE.md`, `docs/DAG.md`,
`docs/index.html` and the frflow and scala-fp skills.

**Stubs by step** (40 `???`, `review.md` lists the first ones the owner will meet): step 2, `derives BoundaryOps`, and
`Flow`'s `collect`, `fold`, `parCollect` and `attempt` (not yet written at all); 3, `feasible`, `commutes`, `made_` of
a program's result, module layouts, a few `LowerProg` steps; 4, `FlowInterpreter`'s loops and errors, `Literals` of
maps and sets, `CodeSyntax.code`; 5, `ModelTests.of`, derived generators, shrinking, the examples' runner; 6, three
review functions; 8, the port interpreters, `NodeChecker`, the lexer's passes; 9, `FrFlowApi.make`, `Views.tree`,
`Views.inbox`.

**Seeded bugs after the port.**

| Example | Seeded today | Stopped today by | Caught after the port by |
|---|---|---|---|
| auth | `careless` decision code | `ContractViolation` | a failing case of the claims on `admit` |
| keycloak | `dropping` store | `ContractViolation` | a failing case of `StoreKeepsState` |
| keycloak | `leaky` introspection | `ContractViolation` | a failing case of the introspection claim |
| crm | `leaky` read | `ContractViolation` | a failing case and example of the read claim |
| crm | `relabel` read | failing examples | failing examples |
| crm | SQL `WHERE` dropped | `ContractViolation`, generated tests | generated tests against `storedMatching` |
| crm | `careless` write | `ContractViolation` | a failing case of the write claim |
| crm | `dropping` database | `ContractViolation` | a failing case of `StoreEdits`; the model test |
| sharing | fault sweep, interleavings | generated runs | the same, over the recorded programs |
| rooms | the README's three changes | `check`, review | `check`, review (`WalkthroughSuite`) |

## 10. Risks and open questions

### 10.1 Risks

| Risk | Likelihood | Mitigation |
|---|---|---|
| Lean proofs are still written per node | certain | none here: FrFlow derives obligations and witnesses, not proofs |
| a lowering differs where an example relies on today's printer | medium | the reference Lean; `Old.claim ↔ New.claim` per node; proofs ported |
| two FrFlows in one build during the rebuild | certain | `next/` gets no feature today's code lacks; today's gets fixes only |
| tagless programs read differently (sharing's 3,247 lines) | medium | sharing last, after each combinator's recording test |
| compile time: rooms 1.3 times slower from clean (10.3) | medium | one helper per operator, macros only where written, measured per port |
| a derivation at every use passes the JVM's limits | seen, fixed | `LeanType` derived once per type; sharing's file compiles in every build |
| renaming a val renames its node | certain | `review` shows a gone node and a new one with the same content |
| a claim meant as a call is tested whole | low | `show` says how each claim is checked |
| a claim with no Scala value is not tested (rooms' root words) | certain | `show` and `status` say so; rooms proves its one from its parts |
| an `always[T]` rule with no Scala value cannot be drawn | medium | state it in evaluable words and prove the link |
| no witness derived for a sound group | medium | "consistency not proven" is a status; add an equation, value or proof |
| the outside facts are many to write (rooms: five) | certain | each is one sentence; a missing one is named with what to say |
| an outside vocabulary lacks a native interpreter | low | it runs through its meaning in the core, a law tying the two |
| a bug only production data shows | certain in principle | the owner's decision; seeds include the examples' worlds |
| the examples' decisions are lost | certain | old `why` texts offered as reasons; `confirm` batches |
| the macros meet a case the examples lack | medium | `ElabError`s name the site; `BoundaryOps` tested per example |
| rewriting 5,176 lines of tests lets a case slip | medium | ported suites keep case names; a step lists what it drops |

### 10.2 Open questions

In order of value; none blocks a step.

- **Step 5: drawn values must meet their fields' rules.** Lean assumes `always[Booking]` of every booking inside a
  `RoomBookings`, but `Respecting` applies only the top-level rule; `CalendarSuite` uses a hand-written `Draw`. Step
  5's derived generators must respect every `always[T]` of every `T` inside a drawn value, with a test that a drawn
  `RoomBookings` meets `endsAfterStart` for each booking.
- **Step 11: the README's forms.** `outside.calls(book)` should name what it guarantees, or `show` spell out the rules
  it covers (`book.calledOnlyWith(endsAfterStart)` would change the formula: the owner's call); `checkedAgainst`'s
  parameters could say their roles (`startFrom`, `readBack`); introduce `World` where first used; `Calendar` should
  filter by the request's room rather than group, or the rule say "of one room"; warn when a node reached by an edge
  is missing from the `KnowledgeBase` list, or collect the list.
- **Step 11: names shared with today's library.** Today's library is renaming the store (`bookingTable`,
  `storedBookings`) and `startsMeetingItsRules`; settle `store`, `stored` and `startsEmpty` at step 11.
- **Steps 1 and 11: rules without a Scala value.** `roomBookingsApart` says "apart" while its rule is `noOverlap`;
  rename it or say so. Make the limit a validation message, not only a risk.
- **Long premise lists (the owner's call).** The store's four facts recur on every claim about the store; an
  assumption could group them, if the owner agrees, still one edge and one kind.
- **The double reading of `always`** (of a type, of a store) is the owner's to keep or split; asynchrony is out of
  scope (owner §17).

### 10.3 Compile time, measured

Today's FrFlow and the planned code each compiled the same code alone, from clean, 15 times in one warm sbt: rooms'
definitions, and sharing's largest match file (26 matches over a 13-case enum) cut down to compile alone. The machine
was shared, so these compare runs back to back:

| Run | First clean run | Median of last 8 | Fastest |
|---|---|---|---|
| rooms, today | 6.0 s | 0.60 s | 0.49 s |
| rooms, planned | 6.4 s | 0.80 s | 0.73 s |
| sharing's match file, today | 12.7 s | 2.44 s | 1.95 s |
| sharing's match file, planned | 12.1 s | 2.38 s | 2.10 s |

Type errors inside a define and `==` on terms give the same messages as today, naming no interpreter
(`Found: frflow.dsl.term.Term[String]`); a second error on the define's result type stays, since Scala 3 has no
`@implicitAmbiguous`.

## 11. Rules that keep it from decaying

1. **The module graph is in `build.sbt` only**; a new module or edge is approved first.
2. **`ArchitectureSuite`** (munit, about 150 lines) scans imports and package clauses and fails on: a package edge not
   in `project/architecture.conf`; a package cycle in a module; `private[frflow]`; `ThreadLocal`; `cats.effect`,
   `io.circe`, `java.nio.file.Files`, `scala.util.Random` or `System.getenv` in `core`, `dsl`, `proof` or `decision`;
   atomics, `Mutex` or `synchronized` outside `eval.Running` and `FlowInterpreter`.
3. **scalafix `DisableSyntax`** on `core`, `proof`, `eval`, `decision`, `dsl`: no `null` (but `dsl.node.Parent.of`),
   no `var` in classes, no `throw` (but "FrFlow bug" sites, `Failure(fault)` in `Elab`, `ReadRecording`,
   `Term.select`, and `NotEvaluated` where 7.1 says), no `asInstanceOf` outside 7.3's places, no `isInstanceOf`, no
   `@unchecked` outside `eval.Fn`.
4. **Size budgets** in CI against a committed baseline: a change may not add a violation.
5. **Golden files** for every example's Lean, contents, CLI output and the README walk-through, once ported; a change
   is listed in its commit message and approved.
6. **Law suites** for every instance (`Gen`, the monoids, `Deferred`) and every algebra against each interpreter;
   `Flow`'s interpreters agree on the models.
7. **A new feature names its concept**, its IR case or algebra operation, its interpreters, its example and the
   goldens it changes (the pull request template).
8. **The scala-fp review checklist**, plus: no analysis reads printed Lean or source text; no view stores what `View`
   computes; no `Option` field a kind decides; no ambient state; nothing in production checks a call; a new pattern
   joins the table below or is not used.
9. **The owner's concepts stay the only ones** (owner §15): `ArchitectureSuite` pins the cases of `Statement`,
   `NodeKind`, `ValueKind` and the quantifiers; changing them is the owner's decision.

The code uses a few patterns, each written the same way everywhere; one file shows each:

| Pattern | Example |
|---|---|
| Phase | `core/analysis/Validate.scala` |
| Value of | `core/analysis/Shown.scala` |
| Stage type | `core/analysis/Valid.scala` |
| Case per kind | `core/spec/Statement.scala` |
| Gathered from parts | `dsl/build/Declarations.scala` |
| Built later, errors kept | `dsl/kb/Elaborate.scala` |
| Algebra of terms | `core/term/Sym.scala` |
| Interpreter transformer | `core/term/interpret/Forward.scala` |
| Lowering of structure | `proof/lean/lower/LowerProg.scala` |
| Algebra | `project/port/LedgerStore.scala` |
| Capability, two interpreters | `dsl/flow/Flow.scala` |
| Program | `project/program/DecideProgram.scala` |
| Rule per command | `decision/rules/Decide.scala` |
| Derived view | `api/node/NodeViews.scala` |
| Errors as cases | `decision/rules/Refusal.scala` |

## Appendix A. The owner's decisions

The decisions are in `owner-decisions.md`; the right column says where this document applies each.

| § | Decision | Where |
|---|---|---|
| 1 | No `IDEA.md` or numbered questions; the README is prose | 8 |
| 2 A, 5 | Terms concrete for the user, tagless-final inside | 4.2 |
| 2 B | No ambient state | 2.2, 4.2, 7.3 |
| 2 C | Tagless boundaries and programs | 4.4 |
| 2 D | A ground-up rebuild here; today's Lean a reference | 1.3, 9 |
| 2 E | Twelve modules, without `runtime` | 5 |
| 2 F | Code fingerprint by the simple lexer | 6 |
| 2 G | Ledgers start fresh | 6, 9 |
| 2 | No run-time checking | 8 |
| 2 | Flow combinators all kept | 4.4, 9 |
| 2 | A committed, signed list of who may decide | 6 |
| 2 | Nodes have no `why` | 2.1, 8 |
| 3, 4, 7 | README delivery and showcase rules | outside this design; 10.2 |
| 6 | Names from the val, `.refines`, `implies` | 2.1, 4.2, 4.5 |
| 8, 14 | `Operation`/`Open`, then `Declaration` | 2.2 |
| 9 | Rooms' root about booking | 3.4 |
| 10 | One idea per statement, a style guide | 2.1, 2.3 |
| 11 | Several root statements | 2.5 |
| 12, 13 | One statement form, no subject parameter | 2.1, 2.7 |
| 15 | Three node kinds, two value kinds, two quantifiers, consistency | 2 |
| 16 | Scope of `always`; outside assumptions; `&&` a style guide | 2.3, 2.6 |
| 17 | Atomicity assumed; asynchrony out of scope | 2.6 |
| 18 | Examples as tests; consistency and vacuity | 2.8 to 2.10 |

## Appendix B. Today's library, and where each problem is addressed

Today's modules (main lines): `model` 5,153 (the DSL, IR, Lean printer, evaluator, validation, run-time wiring,
tests), `lean` 1,340, `check` 1,233, `cli` 1,168, `ledger` 975, `protocol` 758 (wire types, but also ledger logic and
hashing), `api` 686, `agent` 528, `web` 167; tests 5,176 lines, the examples' 1,226. The module graph is acyclic, but
`model`'s twelve packages are one strongly connected component, every module's sub-packages form a cycle, `model`
depends on `protocol`, and `lean` on `model`'s test configuration (`dependencies.txt`).

| Problem | Addressed by |
|---|---|
| P1. No IR between front end and back ends | algebras, one printer, one evaluator; the IR for analyses (4.2, 4.3) |
| P2. A string-typed Lean back end | the Lean AST, `LeanTerm`, lowering over `Prop`; the read-back law (4.8) |
| P3. One `Node` class for every kind | `Statement` cases; edges, positions, code apart; no `why` (2.1, 4.5) |
| P4. `KnowledgeBase` a god object | `Theory` (five fields), `Resolved`, `testing.Settings` (4.1) |
| P5. The core depends on the wire format | `wire` depends on the domain (5) |
| P6. The ledger's node is the wire record | `Subject`, `Standings`, `Shown` (6) |
| P7. Package cycles, visibility bounding nothing | a top package per module; the architecture test (5, 11) |
| P8. Duplicate representations | one `Ty`, `TestReport`, `Shown`, `OpSig`, content form, fingerprint |
| P9. An untyped core (133 casts in `model`) | typed algebras, derived eliminators; thirteen named casts (7.3) |
| P10. Ambient and global state | HOAS binders, values passed, recordings in their own `State` (7.3) |
| P11. Content assembled from raw text | one `Content` form; the lexer's fingerprint (6) |
| P12. Views as flattened copies | `NodeView` by concept, `Tally`, the snapshot by kind (4.10) |
| P13. Errors thrown from the model | `Fault`, `ElabError`, `Problem`, `ValidatedNec` (7.1) |
| P14. Effects not in algebras | algebras with in-memory interpreters (7.2) |
| P15. A DSL wider than its users | run-time features removed; combinators kept with uses (8) |
| P16. Behaviour pinned only on fixtures | the reference, `PortSuite`s, then goldens (9) |
| P17. Two statements of the purpose | `IDEA.md` removed; reasons in signed decisions (8) |

## Appendix C. Sources

Nanopass compilers (Sarkar, Waddell, Dybvig, ICFP 2004; Keep, Dybvig, ICFP 2013) and Scala 3's miniphases (PLDI 2017):
a type per stage, typed trees. Nystrom, *Crafting Interpreters*: back ends as interpreters. Najd and Peyton Jones,
"Trees that grow": considered, not taken. Kiselyov, LNCS 7470, and Carette, Kiselyov, Shan, JFP 2009: section 4.2;
Axelsson and Claessen's circular programs: not needed. Chiusano and Bjarnason: operations and laws first. Bernhardt's
functional core, imperative shell, and ports and adapters (Cockburn, Seemann): pure phases, a thin shell. Parnas,
Ousterhout, Hickey: one hidden decision per module, a node's five facts stored apart. Wlaschin: stages as types.
Fowler and Young: review as a fold of an event log. Typelevel practice (Volpe): algebras, `Resource` interpreters, law
suites. ArchUnit is for Java bytecode, so rule 2 is an import scanner plus scalafix.

