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
`FrModel`; a core that depends on the wire format; package cycles everywhere; the same concept represented in
two to five classes (a Lean type, a test report, "proven, tested or assumed"); what the developer decides cut out of
the source text by line heuristics, so a comment edit reopens a node; and `IDEA.md` stating the purpose a second time.
Appendix B lists the seventeen measured problems and where each is addressed.

### 1.2 What it becomes

1. **The owner's concepts, and no others** (owner §15): three kinds of nodes, two kinds of values, two quantifiers, two
   edges. How a claim is checked is derived and shown. The theory is proven consistent, each store's start included, and
   shown not vacuous; examples are tests beside it; the world outside is said by assumptions.
2. **A compiler with a type per stage**: DSL, `Elaborated`, `Valid`, `Resolved`, `Prop`, `LeanModule`, text; every
   phase pure.
3. **Tagless-final terms**: one printer (Lean) and one evaluator (Scala); the IR read only by analyses; the user
   writes a closed `Term[A]`.
4. **Programs over Definitions**: what FrFlow cannot see is a Definition given plain Scala, a stateful one given
   its meaning in Lean by a state model (owner §36); programs are recorded for Lean and run in `IO` in production.
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

- The planned code (450 main files, 10,484 lines; 58 test files, 154 tests) compiles from clean with
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

Each concept: a definition, an example from the rooms model as step 11 ports it, and how FrFlow checks it. Section 3
shows the whole model; the names used before it: a `Booking` is what the booking form sends and what the table stores
(a room, a start and an end; owner §25); `RoomBookings` is a room's bookings as the table gives them; `storedBookings`
is the table's model, holding every booking; `book` is the booking program, taking a `Booking`, and `granted` the
calendar's decision on a request; `apart` and `noOverlap` say two bookings share no time (over moments, and over start
and end times); `free` says a request is apart from every booking held; `booked`, `bookedAfter` and `accepted` are the
Declarations the two roots, `bookWhenFree` and `acceptWhenFree`, are stated over; `nothingElseWrites`, `oneAtATime`,
`bookingsEndAfterStart` and the other premises are the assumptions of 2.6.

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
    granted(held, request) === free(held.bookings, request)))
  .refines(storeWhenFree, answerWhenFree)
  .assuming(bookingsEndAfterStart)
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
final class Stating private (val varies: Set[SymbolName], val closing: Boolean)
```

**What changes with the World** (owner §41, §43, §45). A statement holds in every world meeting what always holds
(the reachable worlds are among them: `cover_` and `start_` show it, 2.3), and what changes with the world is read in
the current one: a model's state (`storedBookings.current`), a program's run (`book(request).result`, the world it
leaves `book(request).after`, read with `storedBookings.in(…)`), a Declaration, a define reading state. There is no
marker. Every Declaration may change with the World; `kb.Varying` reads off the statements which ones Lean must take as
functions of the world: those a statement reads beside something that changes (state, a run, a define reading state,
`isConstant`, or another such Declaration), until no statement adds one. Each statement is read for this with its
leading variables open, so a run of them counts (rooms' `acceptedIsAnswered` alone makes `accepted` change with the
World). Each of those takes the world as its last input (`booked : World → List Booking`, `accepted : Booking → World
→ Prop`); a Declaration no statement reads so is the same in every world whatever it is, so Lean is given it as a value
(auth's `access`, crm's `finds`). This is sound for statements each read in one world: a constant witness is a
function's, and the function's value at any world is a constant one, so consistency is the same; and a proof is
uniform in the Declaration, so one of `parts d → c d` is one of `parts (d w) → c (d w)`. A Declaration, like every
value read without naming its world, is read in the world before any run the statement reads.

What a statement may say, so that its Lean meaning is the one written wherever it is written (semantics review, owner
§45); each refusal is a `Fault` where the statement is closed (4.5):

- **`always` is a node's whole formula** (`Fault.AlwaysInside`). Nested, it would range over every value Lean has,
  made or not, the opposite of a nested `forall`, which ranges over every value that can be made.
- **A rule reads no Declaration that changes with the World** (owner §45 C, `Fault.RuleOverChanging`, naming a
  statement reading it beside the World). A rule holds of values, in no world, so a Declaration it reads is a value.
- **Beside a run, every world read is named** (`Fault.WorldUnnamed`), whether the statement reads the run's result or
  its world after: `t.current` reads `t` in the world before the run, `t.in(p.after)` after it
  (`ofRoom(room).in(book(r).after)`, `bookedAfter(request).current`, `accepted(request).current`). Read unnamed, a
  Declaration or a define reading state would be read before the run while the statement may read as after it (the
  semantics review's `book(r).result implies !ofRoom(r.room).contains(r)`).
- **`.in` reads in a world only what reads the world unnamed** (`Fault.InNamed`): of a value read in a named world
  already (`m.current`, `t.current`, a `val` of one) it would change nothing, and of a run's outcome
  (`book(b).result.in(book(a).after)`) it would drop the run `a`, a sequence written as one run from the world before.
- **The world after one run at most** (owner §45 E, `Fault.AfterOfTwo`). Every run a statement reads is from the world
  it holds in, so two are alternatives, not a sequence; a sequence is a program that does both. FrFlow states safety
  properties: "eventually" (liveness) and sequencing two runs in one statement are out of scope for now.
- **A program that can fail says so on its Definition, and its run is read with both outcomes** (owner §45 B, §46):
  `Definition[Time => Flow[Unit]]("…").failsWith[StoreDown]` (`Definition.Fails`). Applied in a statement it is a
  `Run`, whose `result` is an `Either[StoreDown, Unit]` and whose `after` is the world either outcome leaves (`runs ∧
  fails`), so a statement about it says what a failing run does; read plainly, it would say nothing of the runs that
  fail, and a program that always fails would meet it, which the type no longer allows (`Problem.SucceedingOnly` stays
  for a theory built otherwise). FrFlow checks the declared error against what the proven code may end in
  (`Problem.FailsWithDiffers`: code raising on a Definition declaring nothing, declaring an error it never ends in, or
  another). There is one `Flow` (§42).
- **A value provided where the code runs is not read beside the World** (owner §45 D, `Problem.ProvidedBesideWorld`):
  it is the same in every world. No port reads one so (`rooms.ReviewSuite`). Owner §45 D, that "now" and the
  histories the ports read as provided values are part of the World, is done for crm and keycloak (step 13c, by G2,
  4.4): crm's history and what it holds are its database's model's (`databaseModel.current.events`, `.store`), its
  clock FrFlow's clock model's (`Clock.clockModel.current`); keycloak's history, state and accounts as loaded its
  store's. Each port's `Judged.provided` says how each value it still provides stands (`Ported.OnD`), the suites
  pinning which are open. Time passing (owner §47) is built (step 13d, "Time" in 4.4): crm's clock is the World's
  time, which the world moves on between runs and at each of the clock's steps; sharing's history and "now" are the
  World's, what its store, its mail server and its clock hold and when housekeeping last ran, its deadlines statements
  of every moment over rules of the World, each `cover_` with the code of what the program calls put in (2.7:
  housekeeping keeping `nothingEndedAtHousekeeping` reads what "gone", "open" and "pending" mean as their code), its
  scheduler's tests run on a virtual clock (`ScheduleSuite`). The rule of housekeeping running beside the other
  programs (`housekeptLately`) is stopped, with what takes it as given, an open point for the owner (4.4, "Time").
  Auth's two tables, read in one moment only, stay provided (owner §48). Configuration fixed for the run (keycloak's
  seed, sharing's start) is not "now" or a history and stays provided.

**`isConstant`** (owner §44, §45 A). `t.isConstant`, of any value `t` read in a statement, says that no run of any
program from the world the statement holds in changes `t`, whatever the run's outcome: TLA+'s `□[c ⇒ t′ = t]`, where
`c` is what implies it (`closed(room) implies bookingsOf(room).isConstant`), read in the world before the step. Over a
stretch of steps where `c` holds, `t` stays the same; with no condition, `t` is the same in every reachable world given
one start, a consequence of this and `initially`, not a second meaning. `analysis.Constancy` states it per program:
one equation `∀ x…, match p x… world with | (_, after) => t after = t world` (a program that may fail, of both its
runs) for each program that changes what `t` reads (its proven code writes a model `t` reads, through the defines it
calls; one with no proven code, or every one where `t` reads a Declaration of the World, may change anything). A new
such program adds its equation, so the statement's meaning changes and it comes back to review; the code's `impl`
proves the equations. It rests on the models `t` reads changing only by code and one run at a time
(`onlyCodeChanges`, `atomic`, derived, `Premise`). Of a Declaration, which no code gives a value, it is an assumption
(`d.isConstant`, each input: `∀ x…, (d x…).isConstant`); claimed, it is proven from parts tying `d` to the code's
values, as any claim about a Declaration is; with no program it says nothing (the `vacuous` try shows it). Two
idioms: "a booking once made is never removed", `forall(b => stored.contains(b) implies
stored.contains(b).isConstant)`; "a count never goes down", `forall(n => n <= count implies (n <=
count).isConstant)`. It is refused where no step keeps it (`Fault.ConstantInside`): under `!` or `||`, left of
`implies`, in a condition, of a run, under an inner `forall` (its variable is another binder's), in a define, an
example; a rule, an `initially` and a program's step read no world (`WorldRead`), and code has no `Stating` for it.

A define changes with the World exactly when its body reads state (`shape.Worldly`, read off the body): it takes the
world last, and each call is read in its caller's world, or in the world it names (`ofRoom(room).in(w)`); an `always`
rule (a value's or a store's), an `initially`, a program's step and an operation's meaning read state through their
own values and operations, so a world read there is refused (`Fault.WorldRead`), and an example, a closed fact about
the code, reads no world (`Fault.WorldRead` of an example). A define's body is a value: an `always` (`AlwaysInside`)
or a run (`RunInside`) written in it is refused. Its `forall`s come with what always holds of their variables, as a
statement's do (`Guarded`, 2.3), so a define read inline means what it does named. A rule's own define takes no
guard, nor does what a rule calls, as a rule reads it (it would be about itself); a define a rule calls whose
quantifiers a value rule guards (or that calls one) is lowered twice (`layout.RuleSide`): as written for the rules,
and `<d>_guarded`, every value rule's guard on its `forall`s, for the statements and the defines they call.
A program writes a model's state only through the model's operations (`Problem.WritesState`), so which programs
change a state is read off the operations they call; and an assumed rule about a model's state needs an assumption of
what the state starts in (`Problem.NoStart`). `Stating` carries
the Declarations that change, so each is applied to the current world where it is written; the statements are read
once open (`Stating.probing`) to find them, then elaborated and closed (4.5).

A **Definition** is a value code and programs use, of any type (a function, a program, an operation on a state, a plain
value). It is a `Term` and gets its meaning exactly once, in the FrModel or where it is written:

```scala
val granted = Definition[(RoomBookings, Booking) => Boolean]("whether a request is granted, given the room's bookings")
```

| Written | `core.code.Code` | Claims mentioning it are |
|---|---|---|
| `implementProven(d)(p)` | `Proven`, `ProvenFlow` | proven of `p` in Lean (`impl`) |
| `implementTested(d)(env => code)` | `Tested` | tested on generated cases |
| `stored` gives `op.means(…)`; `implementTested(ops*)(start, observe)(calls)` | `Modelled` | proven on the model in Lean; the Scala tested against the model on generated runs (3.8) |
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

**What FrFlow cannot see** (owner §36: "Custom scala code has the same nature as external app"). There is no
boundary: everything FrFlow cannot see inside is a Definition given plain Scala, whether the code is the project's own
or calls an outside system. Three shapes:

- **A function**, `granted` (`(RoomBookings, Booking) => Boolean`): tested against every claim mentioning it.
- **An operation on a state**, of type `A => Flow[R]` (rooms' `inRoom` and `add`): its meaning in Lean is given by
  a `StateModel[S]`, `object storedBookings extends StateModel[List[Booking]](…)` with `inRoom.means(room => …)` and
  `add.means(booking => …)`, each over the model's state, a field of the World; programs call it as any Definition,
  `inRoom(request.room)`; its plain Scala is tested against the model on generated sequences of calls (3.8). The
  operations of one system are separate Definitions, not a trait (owner §36: "A for now").
- **A Definition known only by assumptions**: plain Scala with assumptions saying what is trusted of it (keycloak's
  `lookup` with `sessionLookup`, crm's `fetch` with `recordsByQuery`). Lean takes it as unknown with the assumptions as
  hypotheses; its Scala is tested against them where a case can be evaluated, trusted otherwise (`show`, `check` and
  `status` say "trusted, not tested", `Assumed.untested`). An operation on a state with no `StateModel` is the same
  case: its assumptions are written as runs (`op(x).result`, `op(x).after`), and Lean takes it as an unknown run that
  leaves each model's field as it was.

Every Definition must have a meaning (`Problem.Undefined`), so nothing FrFlow cannot see goes unchecked; this replaces
owner §30's "a boundary must have a model or an assumption".

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

What always holds is its own claim, never glued into another with `&&`; its rule becomes a define named as the node.
It is placed below the statement whose hypotheses it gives, with `.refines` (2.4: a rule, not a part of the step):

```scala
val neverOverlap = Node.claim("The bookings stored never overlap.")(
  always(storedBookings)(stored => stored.pairwise(apart)))
  .refines(bookWhenFree, acceptWhenFree)
  .assuming(nothingElseWrites, oneAtATime, startsEmpty, bookingsEndAfterStart)

val roomBookingsApart = Node.claim("A room's bookings never overlap.")(
  always[RoomBookings](held => held.bookings.pairwise(noOverlap)))
  .refines(grantWhenFree)
  .assuming(bookingsEndAfterStart)
```

Checked before production only:

- **`always[T]`** is a hypothesis in Lean on every value of `T` a statement is about, including each one a value holds:
  a list's elements, an option's value, either side of an `Either`, a pair's components, the fields of a record or of an
  enum's case, and a world's store (`Guarded`, its guards built by `Guards` from the type). A `T` inside a map, a set or
  a function value is not reached yet, and a model holding one where an `always[T]` applies is refused
  (`AlwaysNotReached`); step 3 walks maps and sets. It is met wherever FrFlow covers the code: `made_<maker>` for each
  proven define, proven program and store operation whose result is or holds a `T`; `cover_<op>` for each program
  writing a store that holds one; at a tested Definition's boundary (inputs drawn meeting it and every `always` nested
  in them, seeds included, `Respecting`, `DrawnSuite`; result checked, `Made`, through the same shapes); `start_<node>`
  for the store's start; values from outside by an assumption of `always` on their type (2.6). `inhabited_<node>` shows
  the rule admits a value.
- **`always(stored)`** is a hypothesis on every world a statement is about, kept by each program writing the store
  (`cover_<op>`) from every start (`start_<node>`); that this covers every reached state rests on three store facts
  (2.6): nothing outside the code changes it, it starts as `initially` says, and runs on it are atomic; that its plain
  Scala does what the model does is tested (3.8). A world is one a run starts from or one the statement quantifies over
  (every statement reading the world quantifies over the world it holds in, 2.2, as rooms' roots do): each comes with
  what always holds of the stores' states in it. A `cover_` not proven leaves red the rule and every statement taking
  it as a hypothesis (`Reads.takes`, `ReadProof.kept`), as a `made_` not proven does the steps over what it makes:
  rooms' `storeWhenFree` takes `neverOverlap` on its world.
- **An assumption of `always`** is a rule as a claim of `always` is (2.4, 2.6): the same hypothesis, the same `cover_`,
  `made_` and `start_` asked of the code and the start, and `inhabited_`; only its own truth for values from outside is
  trusted, not proven.

For an `always` A, each `H` below being every `always`'s guard on the variable:

| Obligation | States | Asked of |
|---|---|---|
| `cover_<op>` | every run of the code (what it calls as its code, as for `impl`), from a world meeting every `always`, on inputs meeting theirs, ends in one meeting A | each program writing a store A is about |
| `made_<maker>` of a define `d` | `∀ x₁ … xₙ, H(x₁) → … → H(xₙ) → A(d x₁ … xₙ)` | each proven define whose result A applies to |
| `made_<maker>` of a program `p` | `∀ x₁ … xₙ (w : World), H(x₁) → … → H(w) → A (p_run x₁ … xₙ w).1` | each proven program whose run's result A applies to |
| `made_<maker>` of a store operation | `∀ p (w : World), H(p) → H(w) → A(op_of p w.s)` | each operation on a state whose result A applies to, on its model |
| `made_<code>_call_<i>` | on every path to the `i`th call, under the inputs' and the read states' guards, A of each argument it applies to | each proven program or define calling a Definition given plain Scala (a function or an operation on a state) |

`op_of p s` is `Id.run ((Stored.op p).run' s)`. `made_` is the soundness side of assuming `always[T]` of every value. A
define is never asked `cover_`: it has no run and no world.

**`made_` at the call** (owner §37). An argument proven code hands to plain Scala must meet the rules on its type, since
that Scala is tested only on inputs meeting them (`Respecting`). `Required` walks the steps of each proven program and
the body of each proven define into one `Prop`:

- a bind of a call: ∀ result, guarded by its type's rules;
- a `let`: substituted;
- a branch: `(c → then) ∧ (¬c → else)`;
- `each`, `collect`, `fold`: ∀ x ∈ over;
- failure paths (`Raise`, `Catch`, `Guard`): walked too.

At each call it states every rule whose guard reaches an argument's type, of that argument. Its hypotheses are the
code's inputs with their guards, and the rules of the states the code reads (owner §33).

It is asked at every call, and never left to `cover_` where a model stores the argument, so it is one rule; Lean meets
it at once where the argument is an input. A result of a Definition known only by assumptions is a value from outside:
the rules hold of it only through an assumption of `always` on its type, which the code's checks then list
(`Premise.FromOutside`, 2.6), and a claim of `always` whose guard reaches it is refused (`AssumedMakes`, the step 13c
review's B2: no `made_` is asked of it, so the claim's guard on it would be trusted unproven); at a call, such a
result carries the assumptions' guards only (`CallSites`). A modelled operation's result is guarded by its `made_<op>`, a tested function's by the
test of its result (`Made`).

It is a Lean obligation only: nothing is checked when the code runs (owner §2, §37: "With proof yes, but not at
runtime").

A rule met by generated values needs a Scala value, since draws and the witness search use the evaluator; so rooms
states `roomBookingsApart` in start and end times and proves its link to `neverOverlap`'s moments in Lean
(`room_apart` in `lean-spike/Proofs.lean`). Today's rooms states it over moments (`apart`); the port keeps
`noOverlap`, since every `RoomBookings` drawn for the calendar's tests is judged against it in Scala (`Made`), and a
rule with no Scala value judges every room with two bookings broken.

### 2.4 Edges

```scala
enum Edge:
  case PartOf(part: NodeId, whole: NodeId)
  case Assumes(node: NodeId, premise: NodeId)
  case Replaces(alternative: NodeId, original: NodeId)
```

`.refines(parent)` makes a part: a statement's parts together, with the assumptions it lists, imply it; Lean proves
that step (`complete`, or `impl` for proven code) and checks that each part is needed (`needed_C`). A claim of `always`
placed with `.refines` is a
**rule** below the statement it serves (rooms' `roomBookingsApart` below `grantWhenFree`, `neverOverlap` below both
roots): it sits there in the tree and in review, decided after its parent, but it is no part of the step. What it says
is already a hypothesis of every statement about its type or store (2.3), and it is proven by its own obligations
(`cover_`, `made_`, `start_`), so `complete`, `impl`, `holds`, the tries, the step's refutation and `root_impl` leave it
out (`Refinement.parts` is the stated children but the rules; `Refinement.rules` the rules). `show` and review list a
statement's rules apart from its parts ("Rules it uses"), so "together they make it" lists only the parts its step
is proven from, and say of each rule whether the statement takes it (owner §27). A claim of `always` has no step of its
own (no `complete`), as today.

`.assuming(premise)` makes a premise, the one mechanism for one: an assumption the check rests on
(`Problem.PremiseNotAssumed` otherwise), never a part, so `impl` and the view's parts leave it out. An assumption of
`always` is listed this way and is a rule as a claim of `always` is: listing it adds no hypothesis to a step and no
import (its rule is a define), and the code storing or making values of its type still keeps it (`cover_`, `made_`).
`.replaces(original)` is a decision's link to an alternative. A fact about the outside, or an assumption of `always`,
is never a part (`OutsideAsPart`), and only an assumption says one (`OutsideClaimed`).

### 2.5 Root statements

The root statements are the claims without parents: several are allowed, on any Definitions and Declarations, a
statement relating them included (owner §11). Keeping them a concise few is the author's job, which the agent's skill
says. Validation requires at least one (`NoRoot`), never an assumption, and an acyclic graph whose edges stay inside
it (`DuplicateId`, `AboveItself`, `ParentOutside`, `DesignWithoutParent`, `UnderDesign`). Rooms has two, its purpose
stated over three Declarations: a request is booked (`bookWhenFree`), and accepted (`acceptWhenFree`), exactly when
its room is free for its whole time. Below them, a claim says what each Declaration is in terms of the code (2.7), and
booking's two claims are proven of its program; its claims of `always` are rules below the statements they serve.

### 2.6 Assumptions about the world outside

What the world outside the code does is expected to be assumed: the company's procedures, the outside services and how
they are run (owner §16). Each fact is an assumption node, reviewed like any other, written with one of three formulas
(`core.expr.OutsideFact`). Lean does not state them as formulas: its model of the world is built on them. What values
from outside meet is said differently, with `always` on their type (below).

| Formula | Says | The rule resting on it |
|---|---|---|
| `stored.onlyCodeChanges` | nothing outside the code changes the model's state | every reached state is one a run of the code leaves |
| `stored.initially(held => …)` | what the state's start meets | `start_<node>`: `∀ s, initially s → A s` |
| `stored.atomic` | runs on the state never interleave; each call is one step against calls at once | each run is one step of the world |
| `clockModel.schedule(other)((now, o) => …)` | between runs the world moves the clock's time only to a time the rule allows, given `other`'s state then (owner §47) | `elapse` is taken where it allows; inside a run the time moves freely (4.4, "Time") |

All are said of the `StateModel` (owner §36: there is no boundary). The clock (`Clock.clockModel`) needs neither
`onlyCodeChanges` nor `atomic`: its time is the World's by construction, moved by code's waits and by the world alone,
and moved freely at every step of a run, so runs at once need nothing of it; a check on it rests on its schedules instead
(`Premise.Schedule`), and on its `initially` where a rule reads it. That the plain Scala does what the model
says is not assumed: it is tested on generated sequences of calls (3.8), so today's `behavesAs` is gone, its two
meanings now that test and `onlyCodeChanges`. Which programs change a state is not written: FrFlow derives it from the
code, every program calling an operation whose meaning changes the state (`Premises.writers`), and asks each to keep
the model's rules (`cover_`, `made_`) (owner §31). `show` and review of an `onlyCodeChanges` assumption list the
programs derived to change the state; when a new program starts changing it, the claims of `always` about it come back
for review, naming it.

```scala
val nothingElseWrites = Node.assumption("Nothing but the booking code changes the table.")(
  storedBookings.onlyCodeChanges)

val startsEmpty = Node.assumption("The table starts empty.")(storedBookings.initially(stored => stored === Nil))

val oneAtATime = Node.assumption("Bookings are processed one at a time.")(storedBookings.atomic)

val bookingsEndAfterStart = Node.assumption("Every booking ends after it starts.")(
  always[Booking](b => b.start < b.end))
```

Checked: which facts a check rests on is derived (`Premises`), only to check the `.assuming` list the source writes. A
claim about a program's runs rests on `atomic` of each model whose operations it calls; an `always(stored)` also on
`onlyCodeChanges` and `initially`; an `always[T]` on the facts of each model whose state holds one; and any check on
what values from outside meet, where its Lean form carries it (below). A missing fact is refused, naming it and the
assumption that says it (`PremiseMissing(id, needs, by)`), as is one not needed (`PremiseNotNeeded`). Atomicity is
assumed this way (owner §17, §32, §36); asynchrony is future work. A claim resting on an operation's plain Scala doing
what its model does lists nothing: `show` says it rests on that test (3.9).

**Values from outside** (owner §21, §25). Statements are about values, never about a function's inputs. What comes
from outside has a type, and what is trusted about it is an assumption of `always` on that type. The general rule
gives it a type of its own; rooms keeps one type for the README's sake (owner §25): a `Booking` is what the booking
form sends and what the table stores, `bookingsEndAfterStart` assumes every booking ends after it starts, and `book`
takes a `Booking`. The cost: the assumption speaks for every booking from outside, any later source of bookings
included. The rule:

- An assumption of `always[T]` says what the values of `T` from outside meet: those no covered code makes, the inputs
  of the entry Definitions (those whose code no covered code calls) and the values provided where the code runs. Lean
  takes it as a hypothesis on every `T` a statement is about, as it takes a claim of `always`.
- It stands for nothing else. Every value covered code makes or stores, of a type any `always` is about, claimed or
  assumed, is held to `made_<maker>` and `cover_<op>`, proven from the code's inputs and their hypotheses; so an
  assumption cannot hide a bug in the code. Rooms' `bookingsEndAfterStart` is trusted of the bookings the form sends;
  `book` stores them, so `cover_book` is asked of the assumption, and the table's `inRoom` hands bookings on, so
  `made_inRoom` too; code that stores a booking built end first fails `cover_book` (`AlwaysSuite`). What a store
  starts with is said by its `initially` assumption, not by this one: `start_<node>` is asked of it as of a claim.
- A check rests on what values of `U` from outside meet (`Premise.FromOutside(U)`) for each assumption of `always[U]`
  whose guard its Lean form or its obligations carry: on a variable it binds, on a world's store it reads, or on the
  inputs of the makers and programs its `made_` and `cover_` are asked of (`Guards.applies`, `Scope.holds`, as Lean's
  guards are placed). So every statement proven or tested whose Lean takes the rule lists the assumption: in rooms the
  two roots, `storeWhenFree`, `answerWhenFree`, `neverOverlap`, `grantWhenFree`, `grantWhenNoOverlap`, and the two
  rules about a room's bookings, whose `made_inRoom` starts from a world of stored bookings. A root without it is
  refused, `PremiseMissing(id, FromOutside(Booking), Some(bookingsEndAfterStart))`. A claim saying what a
  Declaration is (2.7) has nothing to prove and no code checked against it: it carries the rule and lists nothing.
  An assumption on a type the model uses widely must be listed by every claim it guards; give values from outside a
  type of their own to keep it to the claims about them.
- Premises are never parts, so a claim whose premises are assumptions of `always` is still a leaf, and tested code is
  held to it as to any claim mentioning its Definition (owner §25).
- A claim of `always[T]` whose `T`s can come from outside (an entry Definition's input or a provided value can hold one)
  with no assumption on `T` is refused, `PremiseMissing(id, FromOutside(T), None)`, and what to say is
  `Node.assumption("…")(always[T](x => …))`; listing such an assumption where the check does not rest on it is
  `PremiseNotNeeded`.

No new form, word or kind of node is involved: the assumption is an ordinary `Node.assumption` whose formula is
`always`.

### 2.7 How a claim is checked

A claim constrains every Declaration and Definition it mentions, through its defines too (`Constrained.of`). Its
obligations follow from its formula and from what gives each Definition its meaning:

| When the claim | It gets |
|---|---|
| has parts and no proven code | `complete` (its parts give it, its rules left out, 2.4), and the tries |
| mentions a Definition with proven code | `impl`: the code meets it (but a claim saying what a Declaration is) |
| mentions a Definition with plain Scala | generated cases, per call or the formula whole |
| mentions a fixed or provided Definition | stated for that value, or for every value provided |
| is an `always[T]`, claimed or assumed | a hypothesis; `cover_<op>`; `made_<maker>` per define, program, store operation; `start_<node>`, `inhabited_<node>` |
| is an `always(stored)` | a hypothesis on every world; `cover_<op>` per writer; `start_<node>` |
| is at the bottom (no parts) | a consistency group with what shares its open values (2.8) |
| is at the bottom and mentions a Declaration | says what the Declaration is: no `impl`; the proven code stands in it; its group (2.8) |
| has a condition `A` in `A implies B` | `satisfiable_<i>_<node>` (2.9) |
| rests on the world outside | its `.assuming` list, checked (2.6) |

`impl` is the step of a node whose code is proven (a define, or a program whose run on the models, `f_run`, stands for
the Definition): "∀ U, H → claim[d := code]", `H` its parts or, with no parts, the claims on what its code calls
(`Resolved.reliesOn`). In the planned code a part must be a claim about what the code calls (else `PartNotCalled`). From
step 3b, `impl` takes every part it states as a hypothesis (a design states nothing), the code substituted in it where
the part mentions that Definition: this is sound, since each part is itself checked against the same code and no proof
goes round. A leaf's hypotheses are its `reliesOn` as written, the code not put in: the statements about what its code
calls, leaving out its ancestors, its descendants and every statement about its own Definitions (proven of the same
code, not facts about a callee). A circle that remains over what each node is proven from (`Resolve.provenFrom`: stated
parts, or a leaf's `reliesOn`) is refused (`RestsOnItself`). `PartNotCalled` is dropped (step 3b): narrowed to a part
sharing no Declaration or Definition with the claim or what its code calls, it would still refuse crm's `sharedCrm`
under the root's two expectations and 16 of sharing's parts, sound hypotheses all. `complete` is not asked of it.
Neither `impl` nor `complete` takes a rule (an `always`, claimed or assumed) as a hypothesis: Lean has its rule on every
value already, and its own `claim` is not stated as a fact.

**`cover_` is built as `impl` is** (a choice of the library's, step 13d). The program's run stands with the code of
everything it reaches put in (`Callees.within`): each callee whose meaning is proven code (a define, or `implementProven`)
as that code, a fixed value as its value; a callee tested, assumed or provided stays open, and what is said of it enters
only as a hypothesis, as `impl`'s `reliesOn` gives it (`Resolve.constrainingCalled`), each with the same code put in
where it mentions a callee. So what a program keeps follows from what its callees do, not only from what is promised of
them: housekeeping keeps sharing's `nothingEndedAtHousekeeping` by tidying as its code does. No hypothesis is the rule
covered or rests on it (`Reads.restsOn`: the rule itself, or a claim taking the rule, or one among what such a claim is
proven from), since the rule would then be kept by being assumed; an assumption taking the rule is trusted and rests on
nothing (`CoverCircleSuite`: the picking's claim, read where every stamp is not negative, is no hypothesis of that
rule's `cover_picking`). Each `cover_` also takes every other rule on the stores the program reads, on the world it
starts from, and each `made_` the rules on the maker's inputs and world: the rules are kept together, so a statement
is kept only as each rule its obligations take is, all the way down, and is unproven (`Unproven.Kept` of each open
one) while one is not. A rule is open while its own standing is not proven, for any reason (`ReadProof.local`: its
check, a `cover_`, a `made_` or its `outside` (below) among it; its tests; its consistency, its `start_` among it), or
while a source of its values leaves it open: a value no rule allows (its `inhabited_` not proven: a statement taking
it is proven of nothing), a test of tested plain Scala making a `T` failing, missing or stale, or none at all (the
search stops at the first failing case, the post's perhaps, so the rule broken may go unnamed; a maker no node is
tested against is never tried against the rule, the seventh pass's S7-N1; tested code handed a `T` makes none:
what it is handed is drawn meeting the rules, or a proven caller's, asked at the call), a model run of its store's
Scala failing. One condition, not a list of reasons, so a reason added to a node's standing opens the rules too (the
step 13d re-review's R-B1, the probe `Leans`: a copy of `x` kept zero by taking `x` zero, while a bump breaks it; the
third pass's R3-B1, `MadeLeans`; the fourth pass's P4-B1, `Starts4`; the fifth pass's P5-B1, `Sources5`; the sixth
pass's P6-B1 and P6-B2, `Six`: a maker's test failing on its post first, a store's Scala failing its model test). A
rule open only through another is named by that other (`Kept` names where the standing fails). The rules are kept
together, a joint induction, so a cycle of rules each proven of its own is settled proven. A failing `inhabited_`
stays a warning of its own besides. What each kind takes is said once, where the kinds are
(`Obligations.takes`, one case per kind): `impl` the rules the node's claim takes (`Reads.taken`: its variables, its
`isConstant`'s equations, the worlds it reads, the `forall`s of the defines it reads); `complete` and `feasible` those
and the rules on the values provided where its parts' code runs, its open terms (`Lowering.provided`, the fourth
pass's P4-N1: auth's `o_sessions_0`); `root_impl` of a root its claim's, each root's conjunct under its own guards, and
the rules on what is provided below it; `cover_<op>` the run's inputs and the world it starts from, of `elapse` every
store's (`Reads.coverTaken`); `made_<maker>` the maker's inputs and world, `made_<code>_call_<i>` the calling code's
and every value rule; `outside` the assumptions on the values from outside; `commute_`, the tries, `start_`,
`inhabited_`, `consistent_`, `satisfiable_` and the examples none (two steps from any world; a refutation; the
`initially`s; witnesses).

**Values from outside.** A claim of `always[T]` whose `T` a value from outside can hold (an entry Definition's input,
a value provided where the code runs: `Premises.fromOutside`, the reading `FromOutside` premises and the guards on
provided values already use; an operation known only by assumptions gives values from outside too, which no claim
may cover, `AssumedMakes`) is asked `outside`: `∀ x, assumed x → rule x`, every assumption of `always` on the value's
type a hypothesis. No covered code makes those values, so the claim holds of them only as what is assumed of them
says; before, it was taken of them unasked (the step 13d fourth pass's P4-B2, `Outside4`: positive claimed, not
negative assumed, a zero stored). An assumption on a type holding `T` (a record from outside with a `T` inside) is a
hypothesis of `outside` too, but Validate still asks for one on `T` itself (`PremiseMissing`, the containing type's
judged not needed): conservative, as an assumption on `T` is what the claim lists (the fifth pass's P5-N1, `Sources5`'s
nested probe).

**A step over what makers make.** `complete` takes, for each maker its parts' claims are about, the `made_` of every
rule kept of it (proven of the maker's code) as an `m_<rule>_<maker>` hypothesis, as a caller's `made_` already takes
its callee's `m_<callee>` (`Made.taken`); `holds` and `root_impl` thread the same facts through, and a step whose
`made_` is not proven, or the `made_` of a maker it calls in turn (`Made.resting`), is unproven (`Unproven.Kept`),
so a maker breaking its rule, itself or through its callee, leaves the step red (`SeededSuite`). A `made_` that
rests on the statement being proven (`Resolve.provenFrom` and parts, from what relies on the maker and its callees)
is not taken: no circle. crm's `storeMirrorsRequests` is proven so, given `oneRowPerKey` and `keyedTables` of `save`
and `expire`.
(step 12 ruling)

**What a Declaration is.** A root may be stated over Declarations alone (owner §14), and the claims at the bottom
then say what each is in terms of the code: rooms' `bookedAfterIsStored` says what is booked once a request is handled
is what the table holds after `book` runs. Such a claim (no parts, mentioning a Declaration) is never asked `impl`,
even where it mentions proven code: for every meaning of the Declaration that is false. It is the Declaration's
meaning: the proven code stands in it for the Definitions it mentions, its consistency group (2.8) shows some meaning
of the Declaration meets it, and `root_impl` takes it as what the Declarations are, not as something trusted of the
code. Nothing is proven of the code from it, and it lists no premise (2.6). It is derived, not a kind: an ordinary
`Node.claim`.

**A claim read as a call.** Where a claim applies one Definition to exactly its leading `forall` variables (alone, or
one side of its equation) and mentions it nowhere else, `CallForms` reads it as a call; a program's claim
`forall(request => storedBookings.in(book(request).after) === …)` reads as a run (closed, 4.5, as `∀ request world,
match book request world with | (result, after) => …`), with a failure clause where the program is declared to fail
(`.failsWith[E]`, owner §46: `p.result` is an `Either[E, R]`, closed as both outcomes, `runs ∧ fails`, the `Either`'s
`Right` the result of a run that succeeds and its `Left` the error of one that fails, each side's post its branch as
written; `p.changesNothing`). Another Definition on the same variables is an ordinary mention. A program's error is
part of its type (`Ty.FlowOf(result, error)`, 4.4), declared where the Definition is written and checked against its
code (`FailsWithDiffers`, 2.2): a run's post is asked of its `Except.ok` results, its failure clause of the others.

```scala
enum CallForm:
  case Call(op: SymbolName, post: Written[Lambda])
  case Run(op: SymbolName, post: Written[Lambda], failure: Option[FailureClause])
```

The post is the formula with its leading `forall`s opened (`Opened`): a lambda over the call's inputs (for a run, its
result and worlds too), the Definition a symbol given the call's result when checked. A claim that reads as no call is
tested by evaluating the whole formula on drawn variables; one with no Scala value (a quantifier over a whole type) is
"not checked", and `status` warns when nothing else checks it. `Checking.of(theory, id)` derives the lines `show`
prints (3.9); `Shown.of` says whether each piece of code is proven, tested or assumed.

### 2.8 Consistency

The statements must be proven non-contradictory: some meaning of every open value makes every claim and assumption
hold (owner §15, §18).

- **Groups** (`Consistency.of`): the bottom statements (stated, over every possible value, no parts) and the assumptions
  beside them, joined while they share an open value (a Declaration, or a Definition no proof or fixed value gives a
  meaning). A statement's open values include those of the proven code standing in it: rooms' `bookedAfterIsStored`
  mentions `book`, whose program calls `granted`, so it joins `acceptedIsAnswered` and `grantWhenNoOverlap`. Each
  group is `consistent_<i>`: for every value provided, some meaning of each open value makes each
  statement true. Statements above follow by proven steps, so consistency is carried upward. Each `always` about a
  store, claimed or assumed, gets `start_<node>`. `complete`, the CI gate (4.10), requires every `start_` proven
  (`Warning.StartNotProven` until then); an `always(stored)` with no `initially` assumption has no start to prove it
  from, so a model holding one is never complete. Every `consistent_<i>` must be proven too (owner §28, below). A
  bottom assumption with no open and no provided value is in no group: every word of it has the code's meaning, so
  it is asked `impl` as a claim is (2.7) and is red until proven (`SeededSuite`'s `Trusted`). One with no word at all
  (`∀ xs, xs.length ≠ 3`) says nothing of the world, so nothing justifies trusting it: it is asked to be proven, with
  nothing standing in it, and is red until it is (`SeededSuite`'s `Pure`).
- **Witnesses**, derived where possible, the group solved in substitution order: `∀ xs, s(xs) = e`, `e` mentioning
  nothing still open, gives `fun xs => e`; a bound gives the bound (one past a strict one); a witnessed value then
  stands for itself in the rest. Proven code is its own witness, once what it leaves open is solved: `bookedAfter`'s
  witness, the table after `book` runs, waits for `granted`'s, which `grantWhenNoOverlap`'s equation gives. An
  equation read through a run (`bookedAfter(request).current === storedBookings.in(book(request).after)`) gives its
  witness over the run's outcome. `Equations.defining` reads the shape off the IR; `Defining` builds the term.
- **Pinned provided values.** A provided value that an assumption of the group equates to a term is solved by that
  equation, like an open value; the provided values no assumption pins stay universal (asked of every value):
  `SeededSuite`'s `TwoPins` (keycloak's state and crm's store, which step 12 solved so, are the World's now, owner
  §45 D); auth's session table, which an assumption only bounds, is asked of every value (`PinnedSuite`). A pinned
  value joins groups as an open one does, so every statement mentioning it is in one group, which solves it once: two
  groups never choose it apart, and an assumption whose only value is a pinned one has a group (`SeededSuite`'s
  `TwoPins` and `Closed`). (step 12 ruling)
- **Code all the way down.** What stands in a group's statements is closed over the code: a Definition with proven
  code reached only through another's code has its code stand too (`Stands`, `Callees.reaching`), and its open
  values are the group's. A value provided where the code runs that the standing code reaches is the group's too:
  universal, as a mentioned one is, given what the assumptions at the bottom about such values alone say (the
  group's `premises`, what the world outside is trusted to give: `∀ k, kPositive k → ∃ …`), and the premises over the
  same provided values have a `consistent_<i>` of their own, some value meeting them all (`Group.Premises`, a list
  none bounds witnessed empty, keycloak's `history`), gating every group taking them (`SeededSuite`'s `Vacuous`).
  A consistency statement never binds by `∃` a Definition with a meaning of its own (proven code, a fixed value, a
  model's operation, an unpinned provided value): one left over is left unbound, and Lean refuses the statement
  (fail closed), so no proof chooses the code's meaning or the world's value (`SeededSuite`'s `Hidden` and
  `Through`). A `feasible` statement
  (`∃ U, C1 ∧ … ∧ Cn`, 4.7) does bind them by `∃`, soundly: it shows only that an authored `complete`, proven for
  every meaning of `U` (code and provided values among them), does not rest on parts no meaning meets; whether the
  parts hold of the real code is their own checks' (`impl`) and their groups' here.
- **Currency.** The consistency check is current while `Whole.lean` and every module it imports are as checked, the
  specs of the statements it states among them (`CheckKeys.whole`): a statement changed alone checks it again.

```scala
enum Witness:
  case Equation(symbol: SymbolName, from: NodeId, picked: Picked)
  case Bound(symbol: SymbolName, from: NodeId, picked: Picked)
  case Tested(symbol: SymbolName)
  case Missing(symbol: SymbolName)
```

- **In Lean** (`Whole.lean`), a witnessed group's theorem gives the witnesses in solving order, each earlier one
  substituted where a later one mentions it. Rooms has two groups: `booked`, as `bookedIsStored` says; and `granted`,
  `bookedAfter` and `accepted`, as `grantWhenNoOverlap`, `bookedAfterIsStored` and `acceptedIsAnswered` say, `book`
  standing as `bookIfGranted_run` (step 11 regenerates `lean-spike/Dump.lean` with them).
- **Status** (`GroupStatus`): `Proven` (Lean checked the witnesses), `Evidence` (only tested Scala stands for a value,
  `Witness.Tested`), `NotProven` (`Witness.Missing`, or witnesses Lean does not accept). Consistency gates the proof
  (owner §28: "lack of it makes the proof red, warning is not enough"): a group that is not `Proven` is a failure, not
  a warning. The whole model's proof is red, so `check` fails and `complete` (4.10) is false; and every statement
  proven from parts over a Declaration is red while a group below it is not `Proven`. Its `complete` takes the claims
  saying what each Declaration is as hypotheses, so two that contradict each other
  (`booked(now) === storedBookings.in(now)` beside `booked(now) === Nil`) would prove any root; only their group shows
  they cannot both hold. What makes a group proven is an equation, a bound, a fixed value, proven code, or the
  developer's proof of `consistent_<i>`; tested Scala alone (`Evidence`) is not. A hand-written proof is how a group
  of promises that are not equations is proven (keycloak's `sessionLookup`, crm's `recordsByQuery`, with today's
  `storedSession` and `storedMatching` as witnesses); an agent may write it, Lean checks it, and the developer decides
  the nodes as usual (owner §39).
- **Of an operation known only by assumptions** (4.4), a group binds the operation, a function of its own model's
  state and its inputs, and a witness is one such function. What is assumed of it reads its own model only
  (`ReadsBeside`): said of another model's state, it would be said of every state of that model beside every one of
  its own, and could hold only of an operation that says nothing (the step 13c review's B1: keycloak's draw, said to
  be fresh against the store's log, held only of an API handing on no sign-in, as its first witness did). A witness
  should show what it is assumed to do can be done: keycloak's hands on a sign-in each time, its token longer than
  any it is shown (`drawn_signs_in`).
- **The contradiction search** (`unsat`, `clash`) is an early refuter only; consistency is never inferred from it.

### 2.9 Vacuity

Positive statements guard against a model that says nothing (rooms' `bookWhenFree` says a free room's request is
booked), and two small proofs more:

```scala
enum Vacuity:
  case Inhabited(statement: NodeId, ty: Ty)
  case Satisfiable(statement: NodeId, i: Int, over: List[Ty])
```

`inhabited_<node>`: some value of `T` meets an `always[T]`, claimed or assumed (an assumption no value meets would make
every statement about `T` hold for nothing), together with every other `always[T]` on that type, so two that contradict
show; and an assumption saying what a store starts in gets one too, some state meeting it (`start_` then gives the
store's rules of it). `satisfiable_<i>_<node>`: each condition `A` of a claim's
`A implies B`, with what is bound above it (`Conditions`), can hold, each variable with what always holds of it as
the claim's own (`Guards`: a value code can make, a world meeting its stores' rules); below a run, of the run that
gives what it reads (`¬ runs(p, ¬ A)`: the run succeeds and `A` holds). A condition about a Declaration is not shown
by a witness, which would choose what the Declaration means whatever the claims say: it is stated, not witnessed; so
is one whose proven code calls code not proven (rooms' `book` calling the tested calendar), which Lean takes as open
and no witness gives. The
witness search (`testing.search.Witnesses`) tries the generators' values first, then small values of each type
(`Small`, SmallCheck-style), each meeting the rules on its type and judged by the evaluator, deterministically, at
most 5,000 candidates. A witness found goes to Lean (rooms: `(Booking.mk "" 0 1)`,
`(RoomBookings.mk "" [])`); a condition no candidate meets is "not shown". Lean is given each constant typed at its root
(`(2 : Int)`, `([] : (List Int))`): an untyped numeral defaults to `Nat`, where `0 - 1 = 0`, and an untyped `[]` or
`none` may not elaborate. Examples may serve as witnesses but are never required. Vacuity is reported, not gated:
`status` shows each `inhabited_` and `satisfiable_` shown or not shown, and `complete` does not wait for them. This is
vacuity only; consistency gates the proof (2.8). A claim with no parts is also tried as a tautology (`vacuous`: it
holds whatever what it speaks of means, `∀ r, accepted r = accepted r`); shown, it says nothing, and `show` says so.

**The idle try, of the roots together.** `idle` asks whether a root is met by doing nothing; it is asked of the roots
naming the same Definitions together: the purpose is met by doing nothing only when every root naming those
Definitions is. A safety root alone met by doing nothing is not a defect: crm's `noCrossTenantRead`, with
`addedIsFound` and `writesLeaveOthers`, passes the try; a model whose roots are all met by doing nothing still fails
it. The other roots are stated as their formulas, not imported (no import circle).
(step 12 ruling)

### 2.10 Examples as tests

Examples are ordinary tests beside the model, not part of any node (`RoomsExamples.scala`):

```scala
class GrantedExamples extends FrFlowExamples(rooms):
  example("back to back: granted"):
    granted(RoomBookings("Oak", List(Booking("Oak", 9, 10))), Booking("Oak", 10, 11)) is true

  example("overlapping: not granted"):
    granted(RoomBookings("Oak", List(Booking("Oak", 9, 11))), Booking("Oak", 10, 12)) is false
```

An example is a closed fact (`core.example.Example(name, givens, fact)`); `example(name, d := v)` sets provided
Definitions. Checked against the code (`ExampleRun`: `OnCode.Holds`, `Fails`, `NotEvaluated`, or `Abstract` for a fact
about Declarations) and against the claims in Lean (`example_<i>`, a try met by `frflow_auto`); one that sets values is
shown "checked in Scala only". A value an example writes that breaks a rule on its type (an `always[T]`, evaluated
on each `T` the value holds, `Made.breaks`) is no value the code is ever given, so the example is refused
(`OnCode.BreaksRule`) rather than judged: on such a value the code is neither right nor wrong (semantics review,
finding 10). An example reads no world and states no `isConstant` (2.2). Nothing depends on examples: the theory and
its Lean are the same without them.

## 3. How a project reads: rooms end to end

Rooms books meeting rooms, in six files: `Domain.scala` (the words), `Book.scala` (the table, its model, the program),
`Rooms.scala` (the nodes, in the order they are named), `Calendar.scala`, `Knowledge.scala` (the FrModel),
`RoomsExamples.scala`. An example's files form a DAG, so that no val is read before it is set, whichever file is
touched first: the words (types, Declarations, Definitions, defines), then the table, its model and the program, then
the nodes, then the FrModel, then the examples. This is the model step 11 ports: today's rooms as the owner left it
(owner §25, §26), in the rebuild's forms. The planned code's rooms (`planned/test/project/frflow/rooms/`) is the shape
first approved, kept as it was.

### 3.1 The domain and its words

```scala
/** What the booking form sends and the table stores. */
final case class Booking(room: String, start: BigInt, end: BigInt) derives LeanType

/** A room's bookings, as the table gives them. */
final case class RoomBookings(room: String, bookings: List[Booking]) derives LeanType

val granted = Definition[(RoomBookings, Booking) => Boolean]("whether a request is granted, given its room's bookings")

val book = Definition[Booking => Flow[Boolean]]("booking a request: whether it was booked")

// Over moments.
val covers = define { (b: Term[Booking], t: Term[BigInt]) => b.start <= t && t < b.end }

val apart = define { (a: Term[Booking], b: Term[Booking]) =>
  a.room =!= b.room || forall((t: Term[BigInt]) => !(covers(a, t) && covers(b, t))) }

val free = define { (bookings: Term[List[Booking]], request: Term[Booking]) =>
  bookings.forall(b => apart(b, request)) }

// Over start and end times.
val noOverlap = define { (a: Term[Booking], b: Term[Booking]) =>
  a.room =!= b.room || a.end <= b.start || b.end <= a.start }

// The purpose: what is booked, and whether a request is accepted. Each is a Declaration, known only by what the
// statements say of it, read in the world as it stands (owner §41). A request is a booking asked for.
val booked = Declaration[List[Booking]]("the bookings made, as the world stands")

val bookedAfter = Declaration[Booking => List[Booking]]("the bookings made once a request is handled")

val accepted = Declaration[Booking => Boolean]("whether a request is accepted")
```

`granted` (2.2) is given its meaning by plain Scala, `book` by a proven program. A `Booking` is both what comes from
outside and what the code stores (owner §25; 2.6). A domain type derives its `LeanType` once, where it is declared; a
use without it says "Plain is not a domain type yet: add derives LeanType to its declaration".

### 3.2 The table's operations, its model, the program

```scala
/** The table's two operations: a room's bookings as it gives them, and a booking added. */
val inRoom = Definition[String => Flow[RoomBookings]]("a room's bookings, as the SQLite table gives them")
val add = Definition[Booking => Flow[Unit]]("a booking added to the SQLite table")

/** The bookings stored, as the proofs see them: every booking, oldest first. */
object storedBookings extends StateModel[List[Booking]]("every booking stored, oldest first"):
  inRoom.means(room => state.get.map(stored => make[RoomBookings](room, stored.filter(b => b.room === room))))
  add.means(booking => state.update(stored => stored :+ booking))

/** The program `book` is: the room's bookings read, the request added when granted, in one transaction. */
val bookIfGranted = program { (request: Term[Booking]) =>
  (for
    held  <- inRoom(request.room)
    booked = granted(held, request)
    _     <- Flow.when(booked)(add(request))
  yield booked).atomically }
```

There is no boundary (owner §36). `inRoom` and `add` are Definitions, separate ones (owner: "A for now"), and the model
gives each its meaning over its state (`Model[S]`: `get`, `set`, `update`, each a `Flow`); `storedBookings.current`
reads the state in the world a statement holds in, `storedBookings.in(book(request).after)` in the world a run leaves. A
program is one `Flow[R]` (owner §42), written as a `for` comprehension: an operation applied, `inRoom(request.room)`, is
a step where one is expected (`Flow.step`, given implicitly). Lean sees what it saw with a boundary: a class with the
operations named as the Definitions, the model's operations as `do` blocks, `World`, and the instance on `StateM World`
(`next/proof/src/test/resources/rooms/Models.lean`, the module `Models`, each class `<Model>.Ops`). The program's run on
the models is `bookIfGranted_run`.

The World is the application at one moment, as the proofs see it (owner §33): code never sees it, and a statement
mentions only the stores it reads, taking only their rules as hypotheses. Adding a store adds a field and brings back
for review no statement that does not read that store (step 11's `PortSuite` tests it).

### 3.3 The world outside

The four assumptions are those of 2.6: nothing but the code changes the table (`nothingElseWrites`), it starts empty,
runs on it are atomic (`oneAtATime`), and every booking ends after it starts (`bookingsEndAfterStart`). FrFlow derives
that `book` is the one program changing the table; that the table's Scala does what `storedBookings` says is tested
(3.8).

### 3.4 The roots: the purpose, over Declarations

```scala
val bookWhenFree = Node.claim("A request is booked exactly when its room is free for its whole time.")(
  forall((request: Term[Booking]) =>
    bookedAfter(request) === when(free(booked, request))(booked :+ request).otherwise(booked)))
  .assuming(bookingsEndAfterStart)

val acceptWhenFree = Node.claim("A request is accepted exactly when its room is free for its whole time.")(
  forall((request: Term[Booking]) => accepted(request) === free(booked, request)))
  .assuming(bookingsEndAfterStart)

// What each Declaration is, in the code: the table, and booking's run.
val bookedIsStored = Node.claim("What is booked is what the table holds.")(booked === storedBookings.current)
  .refines(bookWhenFree, acceptWhenFree)

val bookedAfterIsStored =
  Node.claim("What is booked once a request is handled is what the table holds after booking it.")(
    forall((request: Term[Booking]) => bookedAfter(request).current === storedBookings.in(book(request).after)))
  .refines(bookWhenFree)

val acceptedIsAnswered = Node.claim("A request is accepted exactly when booking it answers booked.")(
  forall((request: Term[Booking]) => accepted(request).current === book(request).result))
  .refines(acceptWhenFree)
```

Each root is one equation over a request, holding in every world as it stands, which comes with what always holds of the
table (2.3); the three Declarations change with the World, since `bookedIsStored` reads `booked` beside the table and
the roots read the others beside `booked` (2.2), so Lean has `∀ request world, bookedAfter request world = …`. Neither
mentions code: the three claims below them say what each Declaration is in terms of the code (2.7), and booking's two
claims are proven of its program. `bookedAfterIsStored` reads the table after `book`'s run, so it names the world it
reads `bookedAfter` in, the one before the run (`.current`, 2.2), as `acceptedIsAnswered` names `accepted`'s.
`when(c)(a).otherwise(b)` is Lean's `if`. The roots list `bookingsEndAfterStart`: the purpose holds for bookings that
end after they start (owner §25).

### 3.5 What booking does, and what the table always holds

```scala
val storeWhenFree = Node.claim("A request is stored exactly when its room is free for its whole time.")(
  forall((request: Term[Booking]) =>
    val stored = storedBookings.current
    storedBookings.in(book(request).after) === when(free(stored, request))(stored :+ request).otherwise(stored)))
  .refines(bookWhenFree)
  .assuming(oneAtATime, bookingsEndAfterStart)

val answerWhenFree = Node.claim("A request is answered booked exactly when its room is free for its whole time.")(
  forall((request: Term[Booking]) => book(request).result === free(storedBookings.current, request)))
  .refines(acceptWhenFree)
  .assuming(oneAtATime, bookingsEndAfterStart)
```

Both read as runs of `book` and are proven of `bookIfGranted` by `impl`; a run has no "nothing" to give, so neither
gets an `idle` try. `neverOverlap` (2.3) is a rule below both roots: every world they are about holds bookings that
never overlap, kept by `cover_book` from the empty start.

### 3.6 The calendar

```scala
val grantWhenFree = Node.claim("A request is granted exactly when its room is free for its whole time.")(
  forall((held: Term[RoomBookings], request: Term[Booking]) =>
    granted(held, request) === free(held.bookings, request)))
  .refines(storeWhenFree, answerWhenFree)
  .assuming(bookingsEndAfterStart)

// What always holds of what the calendar is given: hypotheses of the claims about it.
val bookingsOfTheRoom = Node.claim("A room's bookings are all of that room.")(
  always[RoomBookings](held => held.bookings.forall(b => b.room === held.room)))
  .refines(grantWhenFree)
  .assuming(bookingsEndAfterStart)

val roomBookingsApart = …   // 2.3

val grantWhenNoOverlap = Node.claim("A request is granted exactly when it overlaps no booking of its room.")(
  forall((held: Term[RoomBookings], request: Term[Booking]) =>
    granted(held, request) === held.bookings.forall(b => noOverlap(b, request))))
  .refines(grantWhenFree)
  .assuming(bookingsEndAfterStart)
```

`grantWhenFree`'s step is `complete` from `grantWhenNoOverlap` alone: its two rules are no part of the step (2.4), and
what they say, with `bookingsEndAfterStart` of each booking, are hypotheses on `held` and `request` in Lean. They are
proven of the table's `inRoom` (`made_inRoom`), on a world of stored bookings that never overlap. `granted` is the
README's binary search (`Calendar.scala`):

```scala
final class Calendar(held: RoomBookings):
  private val startOrder: Ordering[Booking] = Ordering.by(_.start)
  private val byStart = held.bookings.sorted(using startOrder).toVector

  def grants(request: Booking): Boolean =
    val i = byStart.search(request)(using startOrder).insertionPoint
    val before = byStart.lift(i - 1)
    val after = byStart.lift(i)
    val endsInTime = before.forall(_.end <= request.start)
    val startsAfter = after.forall(_.start >= request.end)
    request.room != held.room || (endsInTime && startsAfter)
```

It is correct as stated on what the table can give (`CalendarSuite`): on 500 generated cases meeting what always holds
(over 50 with two bookings of one room) it meets `grantWhenNoOverlap`; on a list the table cannot give (Oak 0–10 and
Oak 1–2, a request for 3–4) it is wrong, and that list breaks `roomBookingsApart`, so no case draws it; the
README's step-4 calendar, which forgets the booking after the request, is found by a generated case.

### 3.7 The FrModel

```scala
val rooms = FrModel("Rooms")(bookWhenFree, acceptWhenFree, bookedIsStored, bookedAfterIsStored, acceptedIsAnswered,
  storeWhenFree, answerWhenFree, neverOverlap, grantWhenFree, bookingsOfTheRoom, roomBookingsApart, grantWhenNoOverlap,
  nothingElseWrites, oneAtATime, startsEmpty, bookingsEndAfterStart)
  .implementProven(book)(bookIfGranted)
  .implementTested(granted)(_ => (held, request) => Calendar(held).grants(request))
  .implementTested(inRoom, add)(start = BookingsTable.holding, observe = _.bookings)(t => (t.inRoom, t.add))
  .withGenerator(roomNames.describedAs("Oak or Elm"))
  .withGenerator(requests.describedAs("requests for Oak or Elm that end after they start"))
  .withGenerator(roomBookings.describedAs("a room's bookings, laid end to end, some back to back"))
```

Sixteen nodes: two roots, three claims saying what the Declarations are, booking's two claims, four claims about the
calendar and the rules below them, `neverOverlap`, and four assumptions.

`withGenerator` (owner §26) gives a type's generator: `requests` draws bookings that end after they start, and
`roomBookings` a room's bookings laid end to end; every other type's is derived. `inRoom` and `add` get their Lean
meaning from `storedBookings` and their Scala from `BookingsTable`, the SQLite table (3.8).

### 3.8 The table's Scala, tested and run

The SQLite table is tested against the model, not trusted. The FrModel's line (3.7) says how:

```scala
  .implementTested(inRoom, add)(start = BookingsTable.holding, observe = _.bookings)(t => (t.inRoom, t.add))
```

`start` makes the implementation holding a state of the model; `observe` reads its state back; the last gives each
operation's Scala, in the order the Definitions are listed. `ModelTests.run` runs generated sequences of calls
(`Runs`, values meeting each `always[T]`) on both and reports the first answer that differs (`Difference.Answer`) or a
final state that does (`Difference.State`), on 200 runs by default; then each run's first two calls at once on
the Scala, what it gave each and the state it then held being what one order of the two gives on the model
(`CallsAtOnce`, `Difference.AtOnce`; the model's `atomic`, 4.4). It is one form whoever wrote the Scala, the project
or an outside system's vendor (owner §36), so `checkedAgainst` and `implementedBy` are gone. `StoreModelSuite` runs the
same test on an in-memory stand-in and its seeded variants (`ModelTests.of(storedBookings)(start, observe)(calls)`): on
200 runs the stand-in agrees; one that forgets the room filter is found at `inRoom`, one that forgets to add by its
state. The suite also runs `bookIfGranted` in `IO` over `eval.Running` with the table's Scala bound
(`run <- rooms.running[IO](storedBookings := table)`, then `run(bookIfGranted)(request)`), as production does: a free
request is booked, a clash is not.

### 3.9 What check and show say

`show` prints how each statement is checked, every line derived (`CheckingSuite` pins them at step 11; some nodes'
lines elided):

```text
storeWhenFree         proven of book's program, bookIfGranted
                      assumed by the code calling book
                      rests on inRoom and add's Scala, tested against storedBookings
                      rests on runs on storedBookings being atomic: oneAtATime
                      rests on what each Booking from outside meets: bookingsEndAfterStart
bookedAfterIsStored   says what bookedAfter is: book's program, bookIfGranted, stands in it
                      consistent with acceptedIsAnswered, grantWhenNoOverlap: witnessed, for Lean to check
grantWhenNoOverlap    tested against granted's Scala on generated cases
                      assumed by the code calling granted
                      consistent with bookedAfterIsStored, acceptedIsAnswered: witnessed, for Lean to check
grantWhenFree         proven from its parts (grantWhenNoOverlap)
                      rules it uses: bookingsOfTheRoom, roomBookingsApart, bookingsEndAfterStart
                      not checked against granted's Scala: the statement has no Scala value (it quantifies over
                      every value)
nothingElseWrites     the world outside: nothing but the code changes storedBookings; the programs changing it,
                      derived: book
oneAtATime            the world outside: runs on storedBookings never interleave
```

Lean is asked `complete` of the two roots (authored: the two Declarations' claims and booking's claim give each) and
of `grantWhenFree`; `impl` of `storeWhenFree` and `answerWhenFree`; `cover_book` of `neverOverlap` and of
`bookingsEndAfterStart`; `made_inRoom` of `bookingsOfTheRoom`, `roomBookingsApart` and `bookingsEndAfterStart`; two
`consistent_`; `start_` of `neverOverlap` and `bookingsEndAfterStart` (by `frflow_auto`); four `inhabited_`; the
examples. `root_impl` states both roots of the code, given what the Declarations are (the three claims saying so) and
trusting `grantWhenNoOverlap`, tested. `storeWhenFree`'s `impl`:

```lean
/-- Every result of bookIfGranted_run meets storeWhenFree, given what grantWhenFree promise. -/
@[frflow_defs] def impl : Prop :=
  ∀ (granted : RoomBookings → Booking → Prop), ∀ (h_grantWhenFree : (Rooms.grantWhenFree.claim granted)),
    (Rooms.storeWhenFree.claim (Rooms.bookIfGranted_run granted))
```

The table's model is not a hypothesis: it is inside `bookIfGranted_run`. A program's Boolean result is Lean's `Prop`
(`Booking → World → (Prop × World)`), decided by Lean's classical `if`; every request comes with
`bookingsEndAfterStart` as a hypothesis, and every world with what always holds of the table. The proofs of `impl` and
`cover_book` are written by hand: the run's equation, then cases on the answer; the roots' `complete` by rewriting with
the Declarations' claims.

### 3.10 Auth: a purpose over Declarations

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
the three are solved in substitution order. A group nothing ties to the domain is not proven, and the proof is red
until an equation, a value or a proof is added (2.8).
`AuthExamples` sets `grants := …`: "checked in Scala only".

## 4. The compiler

### 4.1 Phases and their types

| Phase | From → to | Where | Effects |
|---|---|---|---|
| construct | the user's vals → `Node`, `Term`, values, `FrModel` | `dsl` | none |
| elaborate | `FrModel` → `ValidatedNec[ElabError, Elaborated]` | `dsl.kb.Elaborate` | runs each lambda once |
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
Kiselyov, Shan, JFP 2009, CKS). **The language is its algebras** (§2.1, §3.2): seventeen over a representation
`T[_]`, bundled by `Sym`; a term is a polymorphic function, the same value for every interpreter:

```scala
trait Sym[T[_]] extends Logic[T], Equality[T], Arith[T], Constants[T], Lists[T], Options[T], Maps[T], Sets[T],
    Eithers[T], Quantifiers[T], Records[T], Sums[T], Functions[T], Named[T], Variables[T], Worlds[T], Annotations[T]:
  def extension[E[_[_]]](key: Ext[E]): Option[E[T]] = None
```

```scala
type Final[A] = [T[_]] => Sym[T] => T[A]
```

The algebras: `Logic`, `Equality`, `Arith`, `Constants`, `Lists` (with `foldLeft`, `pairwise`, `nodup`), `Options`,
`Maps`, `Sets`, `Eithers`, `Quantifiers` (`forall`, `exists`, `always`), `Records`, `Sums` (an eliminator, one `When`
per case), `Functions` (`lam`, `app`, `let`), `Named` (`param`, `define`), `Variables`, `Annotations` (`noted`) and
`Worlds` (a model's state, a program's `runs` and `fails`, `outside`, and `constant`, `isConstant` as written, which
the FrModel states per program before any back end reads it: `analysis.Constancy`, 2.2). Object types are host types
(`T[Boolean]`, `T[List[Booking]]`), so no interpreter tags a value. **Interpreters** (§3.2), one printer and one
evaluator:

| Interpreter | Representation | Used for |
|---|---|---|
| `proof.lean.term.LeanTerm` | `Scope => LExpr` | every term's Lean, the only printer |
| `eval.term.Evaluate` | `Env => Either[EvalError, A]` | every term's Scala value, the only evaluator |
| `core.term.interpret.ToExpr` | `Int => Expr` | the IR, for the analyses only |
| `Collect` | `List[Annotation]` | what a term declares, and faults |
| `Opened[T]` | `Opening => T[A]` | a claim read as a call, as its post |
| `Guarded[T]` | a transformer of `forall`, `exists` | each `always[T]` as a hypothesis |
| `Retyped[T]` | a transformer of `param` | each symbol at its resolved type (a program's error) |
| `Substituted[T]` | a transformer of `free` | a statement closed over its world (4.5), a define over its world |
| `AtValue[T]` | `Option[T[Any]] => T[A]` | a rule read at one value (a guard, the world a run ends in) |
| `proof.terms.Calls[T]` | the calls a term makes, in order | each call of plain Scala on its path (`made_<code>_call_<i>`) |
| `Forward[T, U]` | a transformer's base | forwarding what a transformer leaves alone |

`Defining` and `Conditions` (in `core.consistency`), `Conjoined` and `CallSites` (in `proof.terms`) and the tests'
`Watching` are transformers too. There is no duplicating interpreter. The IR has a checker, `core.typing.IrCheck`
(every variable bound around it at its binder's type, no level bound twice on a path, every node typed as its parts
are), run on every formula and define after elaboration and after `Resolve` types the programs' errors, and in the
laws: an ill-formed IR is a FrFlow bug where it is made, not in Lean.

**Binders are host functions** (HOAS, §3.2). The evaluator applies one to the value, `ToExpr` to the variable at its
depth (`VarId.level`), and `LeanTerm` names it by the developer's name, or with the first free number when that is
taken (`x_1`), never a name a symbol, the FrModel's or a model's namespace, or a name generated Lean writes itself is
spelled as (`Naming` reserves them as Lean spells them). `core.name.LeanNames` holds every name convention generated
Lean uses, and spells a model's names injectively (`some` is `some_`, `some_` is `some__`, `a$b` is `«a$b»`), so two
names never meet in Lean. Nothing is numbered before an interpreter binds it.

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
`c.on[Change.Book](b => …).on[Change.Clear.type](…)`, each arm named by its case's type and a case without fields by
its singleton type, in any position, the only spelling (the planned code still writes `.on(Change.Clear)` after the
first arm); each arm's type test written by `CaseMacros` (no cast), printed as a `match`; records made
(`make[Booking](room, t, t + 1)`) and copied (`b.updated(_.start, t)`); the folds and `let`; `allDistinct`, `pairwise`
and `forall` of a define; a program's runs. A define is one `term.Body` (name, curried type, a `lam` per input) applied
one argument at a time, so `param`, `define`, `lam` and `app` cover every arity.

**Notes are an interpretation**: what a term declares, and faults, are on the term (`noted`), gathered once by
`Collect` into a monoid (`Declarations`); there is no registry. A project's own operation is a define, or an algebra
outside the core found by a typed key (`Count` in the tests, via `Sym.extension`, falling back to its meaning in the
core).

**What is not compositional** (§2.4, §3.3) reads the initial form (the "what changed" view, the refutation's hint,
the layout, `CallForms`, where a witness sits) or passes context (`LeanTerm`'s scope, `Opened`, `Guarded`, `Calls`).
A field of a record made on the spot prints as its argument, read off the constructor (`LExpr.Ctor`), never off the
spelling of a call. The code fingerprint hashes source, not terms.

**Syntax and laws.** `implies` is alphanumeric, so it binds last; a macro refuses `a implies b implies c` without
parentheses. On 300 generated terms (`TermLawsSuite`, `TypeOfSuite`): a written lambda gives the evaluator's value,
the IR is typed as the term and well formed (`IrCheck`); the printer's text reads back and prints the same
(`PrinterLawsSuite`), and, every binder and symbol named adversarially (Lean's keywords and prelude names, their
mangled forms, the FrModel's and the types' names, the symbols' own: `Renamed`), reads as it does with its variables
named afresh, up to de Bruijn indices, every symbol its IR mentions free as often (`CaptureLawsSuite`). Step 3 shows
that each generated term elaborates in Lean; step 4, with the evaluator, adds the law that Lean decides each generated
term as the evaluator does. `FRFLOW_LAW_SEEDS` (`from:count`) draws the laws' terms from other seeds (CI's nightly).

### 4.3 The IR

`core.expr.Expr`, made only by `ToExpr`, is a simply typed lambda calculus with data, containers and quantifiers; every
node carries what its type needs (`Exprs.typeOf` is total, and `typing.IrCheck` checks each node against its
parts). A binder's id is its level; a recorded step is numbered negative, apart from every level (`VarId`). One
operator per meaning (`Contains` of a list, option or set is one `PrimOp`); every operation with a body is
`Expr.Iterate`. `Mentions`, a monoid, says what an expression mentions.
`Prog[E]` is a program's steps, first order, generic in what a step holds (`Prog[Stated[?]]` for back ends, `Prog[Expr]`
for analyses): a free monad over the operations on a state and the models' state, with errors, loops and concurrent
steps (`Par`, `ParEach`, `Race`, `Guard`, `Atomic`). `Written(value, source, form)` keeps the term or steps (what back
ends read), their IR (what analyses read) and the Scala as written (what the developer decides); only its three makers
build it, so `value` is always `form`'s IR (`failing` only refines a program's IR's type by the error it may fail
with, the steps unchanged). The IR is never printed or run.

### 4.4 Programs over Definitions

There is no boundary (owner §36). A program calls Definitions: functions, defines, and operations on a state
(`A => Flow[R]`), each given its Lean meaning by a `StateModel` (2.2, 3.2). A program is one type, `Flow[R]` (owner
§42), written as a plain `for` comprehension over its steps, its values terms (`dsl/frflow/dsl/flow/Flow.scala`,
excerpt); the steps are an initial encoding, `run.Recorded`, which Lean reads and production folds:

```scala
final class Flow[A](val steps: Recorded[Term[A]]):
  def flatMap[B](f: Term[A] => Flow[B]): Flow[B]
  def map[B](f: Term[A] => Term[B]): Flow[B]
  def atomically: Flow[A]
  def handle[E: LeanType](handler: Term[E] => Flow[A]): Flow[A]

object Flow:
  /** An operation on a state, applied: a step (given implicitly where a step is expected). */
  def step[R](op: Term[Flow[R]])(using LeanType[R]): Flow[R]
  /** One of two programs by a condition at hand; `when(c)(fa)`, the program or nothing. */
  def cond[A](c: Term[Boolean])(ifTrue: => Flow[A], ifFalse: => Flow[A]): Flow[A]
  def each[X: LeanType](xs: Term[List[X]])(body: Term[X] => Flow[Unit]): Flow[Unit]
  def raise[E, A](error: Term[E]): Flow[A]
```

`Flow.scala` also has `guarantee`, `race`, `parTupled` (`(a, b).parTupled`) and `ifM`, `bracket`, `attempt` and
`timeout` made of them; `RecordingSuite` records each as the step Lean reads (with `each`, `raise` and `handle`). A
`for` with an alias (`booked = granted(held, request)`) reads as Scala 3.8's `for` reads it, a `val` in the body of the
step before, so no step is added; the user never sees `F[_]` or an interpreter. Every combinator is kept
(owner §2) and given a use in an example. `collect`, `fold`, `parCollect` and `attempt` (today's `traverse`, `foldM`,
`parTraverse`, `attempt`) are kept as step 2 added them, and today's `retry` and `parTraverseN`'s limit as
`retry(sleep, waits)` (a fold of the waits over `handle` and the clock's `sleep`, as today) and `parCollectN(n)`
(`Prog.ParEach` with its limit). The clock is FrFlow's own three Definitions, `now: Flow[BigInt]`,
`sleep: BigInt => Flow[Unit]` and the world's own step `elapse: BigInt => Flow[Unit]`, with their `StateModel`
(`clockModel`, its state the time now; "Time" below); `timeout` takes `now`, and `retry` `sleep`. A program's steps
have three readings:

- **Lean's**: the steps as recorded, where an operation applied is a recorded call (`Prog.Call` of the model and the
  operation). `program { … }` reads them into `Prog[Stated[?]]` (`ReadRecording`, steps numbered in its own `State`);
  Lean prints a `do` block over `[Monad m]` and each model's class, run on the models' instance on `StateM World`. A
  bound term is shared as Lean's `let`.
- **Production's**: `eval.Running` for any `F: Async`, reached through `knowledge.running[F](bindings*)`, each model's
  Scala bound (`storedBookings := table`), a fold of the steps into `F` (`run(bookIfGranted)(request)` runs a program's
  Definition on its inputs' values, `Spot.Steps`): a condition evaluated by `Evaluate`, `atomically` under one `Mutex`.
  An operation's Scala is plain Scala over plain values (`String => IO[RoomBookings]`, from the FrModel's
  `implementTested(ops*)(start, observe)(calls)`); `Running` evaluates each argument, calls it and makes the result a
  term again. For a model whose operations may fail (`StateModel.failing[S, E](means, error)`), an implementation's
  non-fatal failure is mapped to the declared error (raised as `Raised`, its cause kept); a `Raised` passes through,
  cancellation is never mapped, and a model that cannot fail lets its implementation's exceptions escape as they are.
  Nothing is checked.
- **Scala tests'**: the recorded `Prog` run by `eval.flow.FlowInterpreter` against a `World`: the models (examples,
  model tests) or the implementations (interleavings). A sequential run takes the scheduler's choices from the world (a
  reserved `races : List Bool`, held like `faults`, read by `races.leftWins`), choices Lean leaves open.

**A race** (step 13 review, B1). In production `l.race(r)` runs both sides at once and cancels the loser when the winner
finishes, at whatever step it has reached: what its steps did until then stays. So a race is read, by Lean and by the
sequential runs alike, as the scheduler's choice of the winner (`races.leftWins`), then the loser's steps until the
scheduler cancels it (`Prog.Cut`: before each of the loser's steps the world says whether it is cancelled there, the
next of the same `races`, `true` when none is left), then the winner's (`ReadRecording.raced`). A step is an operation's
call or a transaction, neither of which production cancels part way (`Running` runs each call, as each transaction,
uncancelable, as the concurrent tests' scheduling does; the step 13 re-review's RS1). So any slow call holds a race
until it finishes: a race won beside a call that blocks on I/O returns only when that call ends, and a race is no
timeout for a slow operation. The clock's wait is the one call cancelled inside, so that a race won beside a long wait
does not wait for it: its model moves the clock once the wait is over, so a wait cut short is read as cut before it, and
the time that passed meanwhile is the world's ("Time" below). A traverse at once in the loser has each
branch cancelled at its own step, read in turn, and what follows it dropped when one was (`FrFlow.Races.each`); a race,
a pair at once or a finalizer (`guarantee`, `bracket`) inside a race's side is refused (`RaceSideHolds`): what they do
when cancelled is not read. In Lean the loser is `FrFlow.Races.cut (do …)`, its block in `OptionT`, each step
`FrFlow.Races.step (…)` (the choice, then the step), the rest dropped once a step gives nothing; `frflow_defs` unfolds
it step by step. The loser's steps are read before the winner's, which stands for production's run, where they
interleave, by the commutation of each step of one side with each of the other's (below). Equations of worlds are
refused where a program races, as where a model may fail (`WorldsEqual`): the choices a run takes are part of the world
it leaves. The review's probe (`whole.RaceProbe`: two adds raced against a sleep, "when the sleep wins the box is as it
was") stays unproven, as it is false of production's run (`RaceProbeSuite`, `RacesLeanSuite`), and sharing's delivery is
interleaved whole with sends slower than its limit (`InterleavingsSuite`): every run ends where the reading allows, some
half done. `timeout` is read as written (`now`, the steps, `now`; it does not cancel): the world moves the time on
after each of the clock's steps, so the limit is past exactly when more than its seconds passed between the two reads,
and both outcomes are proven of a program using it (`TimeLeanSuite`'s `firesLate`, sharing's `handleContract`). A
race against a wait (Cats' cancelling form, sharing's delivery) is read as races are; a wait winning it means its
seconds passed (`waitWins`).

**Steps at once** (the step 13 re-review, RB1, RB2). Lean reads a pair's branches, two elements of a traverse at once
and a race's sides one after the other; production interleaves their steps (`F.both`, `parTraverseN`, `F.race`). A
side interleaves at its steps (`core.analysis.AtOnce`): each operation's call, and each transaction whole, which only
another transaction waits for (the one lock), so that a call outside a transaction may come between the calls inside
one. `commute_i` asks, of each pair of steps one of each side that touch a model in common (`AtOnce.pairs`: two
transactions, two calls, or a call beside one inside a transaction of the other side), that the two orders give the
same results and leave the same models from every world. It is asked for every value of the variables each step reads
(each side its own, `x_one`, `x_two`: what the steps before it in its side gave), for a traverse of any two of its
elements (`[one, two]` a sublist of what it is over, either way round: two places, whose values may be equal), and,
where the program may fail, of each step to its own outcome (`FrFlow.caught`), as a step's failure goes to its own
side. Steps on models apart commute by construction (each model a field of the World, `Commute.within`), so nothing
is asked of them; each pair is asked once (of a traverse, either way round). Unproven, the claims of the program are
not proven.

It is sound by Lipton's reduction. A run in production is an interleaving of the sides' steps, each all or nothing
(above) and indivisible against the other side's: a transaction by the lock, a call by its model's `atomic`, which says
each call of the model's operations is one step against calls at once as well as runs (its Scala keeps them apart: one
update of the state, or a store serializing them). That is checked, not only assumed: the model tests run two calls of
each run at once on the Scala and compare what each gave and the state it then held with the model's two orders of them
(`CallsAtOnce`, 3.8), so Scala that reads the state, pauses and writes it back, which passes every run in turn, fails
them (the re-review's P8, `ModelRunsSuite`). Where one of the two is of an operation known only by assumptions, the
model has no answer to put in an order, so the two at once are compared with the Scala's own two orders of them, each
made afresh holding the state before (it is a function of its state, `Difference.Twice`): a lost update is found there
too (the step 13c re-review's R-S1, `ModelRunsSuite`). No lock per model is taken in `Running`, which would cost delivery its
sends at once. Two adjacent steps of two sides that commute can be swapped without changing either's result or the
models after (`Commute.swap`), and what a step does depends only on the models and the values its side gave it. Swapped
two at a time, each side's steps keep their order, so every interleaving becomes the reading's order (the first side's
steps, then the second's), every step giving what it gave: what is proven of the reading holds of the run. A race's
loser cancelled between two of its steps is the reading's loser cut there. The two probes stay unproven, false of
production's runs (`AtOnceLeanSuite`, `InterferenceProbeSuite`): a set raced against a copy of the same number into
another ("when the set wins, b is as it was or holds a's old number": the copy read the new number), and two bumps at
once, each a read then a set ("adds two": one is lost); two sets on two models at once ask nothing and are proven.
Sharing's delivery passes: two of its sends at once are to two people's mailboxes or of one notice
(`Lemmas.sends_commute`), two removals from the outbox are transactions whose filters commute
(`Lemmas.removals_commute`), and its waits at once take the longest of them in either order ("Time" below); handle
reads the time and the library at once, models apart.

**Time** (owner §47: "see how Cats does that"; step 13d). Time follows Cats Effect's model (`Clock`, `Temporal`,
`TestControl`). The clock is FrFlow's model `Clock.clockModel`, its state the time now, a field of the World, which
only moves on by construction: `now` reads it, `sleep(d)` and the world's own step `elapse(d)` move it by `d` and never
by less than nothing (`vocab.Timed` marks it). Steps of code take no time of their own; the world moves the time:

- **Between runs**, by `elapse(d)`, the world's own step (`TestControl.advance`), which no code calls
  (`Problem.OutsideStepCalled`). It is a step like a run for what holds of every reachable world: every rule reading the
  clock is asked `cover_elapse` (the reachable worlds are the start, then any mix of runs and `elapse` steps), and every
  `isConstant` reading it its equation for `elapse` (`Constancy`); a statement or an obligation reads its run as
  `ClockModel.elapse_run`. `stored.onlyCodeChanges` and `atomic` are not asked of the clock (2.6).
- **In a run**, after each of the clock's steps: the next of the world's `ticks : List Nat` (a reserved field, a choice
  of the world's as `faults` and `races` are; none left: no time), `FrFlow.Clock.tick`. After, so that the first look
  of a run that looks first is the world's time (what passed before it is the world's step before the run, and what
  passes after its last look its step after): crm's searches read the world's time, and a statement may say so. A
  look with other steps before it, and no step of the clock's yet, is given a look first, its time dropped, so the
  tick after it is the time passing at those steps (`analysis.Looks`, the step 13d re-review's R-B2: `Late.readsStart`
  stays unproven); a call of a program that may look is given one so too. Between two looks, time passing at a step
  that does not look at the clock is not told apart from passing at the next that does. So two looks in one run may
  differ (`TimeLeanSuite`'s `stampTakesNoTime` stays unproven: a program relying on its run taking no time), and
  `timeout`'s `none` is reached.
- **At a wait**, by at least its seconds: the wait's own move, then a tick. A wait at once with others (a side of a
  pair, a traverse at once or a race) is read as two points (`analysis.Waits`, the step 13 re-review's RN1): where the
  sides start (the time read once before them, a lower bound of every wait's own start in them) and its end, the time
  reaching at least that start plus its seconds (`Prog.reach`, `FrFlow.Waits.reach`). Two such ends commute (each the
  later of two times), so waits at once take the longest, not the sum (`waitsAtOnce` proven, `waitsAddUp` not); a look
  at the clock beside one does not commute, and `commute_i` refuses the pair. This is Lean's reading only: production
  and the Scala tests run the waits as written. The other reading the re-review offered, leaving waits out of the
  reduction, was not taken: sound too, but a wait would then say nothing of the time it took, and a race lost to a wait
  (a cancelling time limit) could not be said to have taken its seconds. Waits in sequence inside one side of a step at
  once are read so too, each from the same start: delivery's retry waits of a second and then two in one branch are
  read as two seconds at least, not three. This is sound (it allows more runs, and the tick after the start covers the
  rest) but loses a lower bound a statement could want (the step 13d review's S3).
- **Where the schedules allow.** A schedule is a trusted fact restricting the outside steps (2.6, owner §47):
  `clockModel.schedule(lastRun)((now, ran) => now <= ran + 120)`, an `OutsideFact.Schedule(model, over, rule)`, its rule
  a define over the time reached and the states of the models it names (no world, no other Definition: Lean reads it in
  the clock's instance, `allows`). It restricts the world's own step between runs only: an `elapse` is taken only where
  every schedule allows the time it reaches (`FrFlow.Clock.move`). Inside a run the world moves the time freely: a tick
  by any amount, a wait by at least its seconds, never less (`LowerEnv.Clock.inside`, `fun _ _ => True`). A run sees the
  World as it leaves it, not as the runs at once beside it change it, and those runs may keep a schedule true while
  this one is in progress (the step 13d review's B1: a five minutes' wait under sharing's schedule takes five minutes,
  `Lapse.quick` stays unproven). A check whose Lean takes the clock rests on each schedule of it (`Premise.Schedule`),
  listed by `.assuming`. A schedule that lets no time pass from the start is warned of: its `frozen` try (`∀` start, `¬`
  a move by `d > 0`) shown, as vacuity is (`TimeLeanSuite`, `Frozen`). So is one over a model no program writes
  (`Outsides.unwritten`, `status`'s `ScheduleUnwritten`, the re-review's R-N1): it lets time pass from the start and
  freezes it once the time reaches its bound (`Unwritten`).
- **Who moves the time.** Every program calling any of the clock's operations, `now` too, changes the clock's state
  (`Premises.writers`): the world moves the time after each of its looks. So an `isConstant` reading the clock is asked
  an equation for each such run (the step 13d review's B2: `Extend.stays` stays unproven).
- **Open (for the owner): deadlines kept by a program running beside the others.** A rule bounding the time by another
  model's state, kept true by a program that runs concurrently with the rest (sharing's `housekeptLately`, `now <= ran +
  120`, housekeeping run every minute beside requests and delivery), cannot be shown when runs are read one after
  another: any other run may move the time without bound. Sharing's `housekeptLately` is stopped (`Judged.stopped`),
  and with it each statement taking it as given where it starts: its three deadlines and the branches above them, the
  claims about the programs' runs over the World (each proven itself), and the World's other rules, whose every
  `cover_` takes it on the world a run starts from (`Reads.coverTakes`; a rule kept from one still open is not kept,
  the step 13d re-review's R-B1, the probe `Leans`), with what takes those. Its scheduler's tests (`ScheduleSuite`)
  still check the deadlines on a virtual clock. How such a rule is to be stated is the owner's to decide.

A rule may relate several models' states (`always(clockModel, lastRun)((now, ran) => ran <= now)`), its `start_` of
each model's `initially` together. `changesNothing` leaves the clock aside: time passes whatever a run does. In Scala the
clock is a virtual one where it is tested (`Wall`: `elapse` moves it, the model tests interleave its calls, `elapse`
among them, on generated runs), and the system's in production, where `elapse` is never called. Crm reads the World's
time; sharing's run is the World's (2.2). What a statement may not yet say: "eventually" and two runs in sequence
(owner §45 E), and so a deadline is a statement of every moment (sharing's `trashPurgedOnTime`), not of a run's future.

What the reduction does not cover is refused (`Validate`): a side that may let an error out beside one that may fail
or changes a model's state (`FailsBeside`; of a traverse, a body that may let an error out). Production then cancels
the others at whatever step each has reached, which the reading in turn does not read; a side cut short that cannot
fail and changes no model has done nothing a statement reads (handle's clock beside its library's load, which may
fail). A race's side holding a race, a pair or a finalizer is refused as before (`RaceSideHolds`).

`StateModel` reads each operation's `means` into `vocab.StateModel` (`ModelOp` per operation); `LowerModels` prints the
models, `World` and each program's run on them (`f_run`). `FlowAgreementSuite` (step 4) states the law that a
program's recording run on the models gives what `Running` gives on the models' instances, a failing implementation
included.

**An operation known only by its assumptions** (G2, ruled within owner §36, "a Definition known only by assumptions is
the assumed case"; built in step 13c). An operation of a `StateModel` with no `means` (`fetch.assumed`) is opaque in
Lean: a constant of its model's state monad, run on its own field of the World through `within` (the model's class's
`onState`), so it touches only its field by construction; a statement's run of it is `Model.op_run`. What is assumed
of it (its runs' results and what it leaves, `forall(q => fetch(u, q).result …)`, `databaseModel.in(fetch(u,
q).after) === databaseModel.current`) is a hypothesis of every obligation of a program calling it, and open where
consistency is asked (a hand witness, owner §39). Its Scala is tested against those assumptions on the model's
generated runs, the model given the state the Scala left (`Difference.Assumed`), as a model's Scala is tested against
its model. It is an operation's meaning left open, not a model kind (§35's `AssumedModel` stays removed). Where a
rule is about its store and nothing says what its runs leave, it is refused (`LeavesUnsaid`, which checks only that
some assumption reads the world it leaves: one saying nothing of it passes, and `cover_` stays unproven), and where its
model may fail (`AssumedFailing`). It is a function of its model's state and its inputs (Lean's binder,
`A → StateM S R`): two calls from one state give one result and leave one state, so a program may rely on two lookups
agreeing, and the model tests call its Scala again on the Scala made holding the state before each call, which must
give and leave the same (`Difference.Twice`: a lookup flipping a coin is found). What is assumed of it reads its own
model only (`ReadsBeside`, 2.8): what it needs of another is handed to it as an input, as keycloak's draw is shown the
requests the store has logged (`nextRequest(handled)`, `drawnTokens` fresh against them, tested on the inbox's runs).
Only its assumptions are taken of it (`Constrained.assumptions`): a claim about it is proven from them (`impl`, asked
of any claim about operations on a state alone, which was asked nothing and stood proven; one about an operation with
steps stays open for now, a statement's run of it not read as its steps), never a hypothesis of code calling it, so
no proof takes as given what it is to show (the review's B3); the circles `Validate` refuses are walked along what each
`complete` and `impl` takes (`Resolve.below`). Its results are values from outside (owner §37, `AssumedMakes`, 2.3).
An assumption about it that its model's runs cannot evaluate (not read as a run of it, or its post with no Scala
value) is trusted, not tested, and `show`, `check` and `status` say so (`Checking.TrustedUntested`,
`Assumed.Untested`, `Warning.TrustedUntested`). Crm's screens are programs calling the database's `fetch` (`recordsByQuery`, `searchKeeps`)
and reading the clock, its write side and expiry job programs over the database; keycloak's server programs over its
store, whose storing and index are assumed (`storeLogs`, `lookupKeeps`): so their histories and what they hold are
the World's (owner §45 D), the rules of what each holds (crm's `crmRun`, `oneRowPerKey`; keycloak's `serverRun`,
`freshTokens`, `oneSignInPerToken`) claims proven of the code that changes it. Keycloak's server reads the log
(`logged`) and hands it to the draw, whose freshness against it is what `freshTokens` is kept by: the two ways the
review suggested do not fit the library, an assumed `always(serverStore)` being held to `cover_` by the code changing
the store (so it would need the same fact of the draw) and a rule tying the inbox's state to the store's being of two
models, which `always(stored)` is not.

**Nothing FrFlow cannot see goes unchecked** (owner §36, superseding §30's and §35's boundary wording). Every
Definition has a meaning (`Problem.Undefined`): proven code, a value, plain Scala tested against its claims, an
operation's model with its Scala tested against it, or plain Scala known only by its assumptions, tested against them
where a case can be evaluated. What proven code hands to plain Scala meets the rules on its type
(`made_<code>_call_<i>`, 2.3), a Lean obligation only (owner §37). `BoundaryUnchecked`, `behavesAs`, `AssumedModel`
and a boundary's call written in a statement are gone: an operation is a Definition, so a statement runs it as it runs
a program, `storedBookings.in(add(b).after)`.

**A program's error type** (step 3b, before step 4). `Ty.FlowOf(result, error: Option[Ty])`. A program's error has two
senses, both read off its recording (`core.Failing`). The monad's: every error it raises, handles or meets (a failing
model's, `StateModel.failing[S, E](means, error)`), one type, what `FlowOf` says and its run is over. What escapes:
those outside a `Catch` of their type (`Progs.failsWith`), what a failing run's clause is of. A model whose operations
may fail names the error a call fails with (`Failure.StoreUnavailable`, `vocab.Fails`), which `FrFlow.failing` needs.
The front end cannot type a program's error where its Definition is written (its code comes later), so `Resolve` does
(`Failing.typed`): each program's define, the Definition it is the meaning of, and every formula's term and IR
(`Retyped`), so `Exprs.typeOf` of a program in a formula is its resolved type. Only a proven program has an error; a
program Definition given plain Scala has the one its type declares (none). `Validate` refuses a program over two error
types (`ErrorsDiffer`; handling one and failing with another, or calling an operation failing with another, would need
two `ExceptT`s), a `.failing` clause of another type than what escapes (`FailingDiffers`), one on a program nothing
escapes (`NeverFails`), and a run of a program that is no Definition applied to inputs (`RunOfNoDefinition`: Lean reads
how to match a run off the Definition it applies). In Lean a program with an error runs as `World → (Except e r ×
World)`, on the models' instance on `ExceptT e (StateM World)` (one per error), a failing operation's call going through
`FrFlow.failing` on the world's `faults : List Bool` (a field when an operation may fail; `faults` and `races` are
reserved); `f_run` is `FrFlow.runOnE (ε := e)`, a run's post matches `Except.ok` (`| _ => True` for the rest, sound when
nothing escapes), `cover_` holds of the world a failed run leaves too when an error escapes (both arms, `runs ∧ fails`,
`FrFlow.outcome` unfolded), `made_` of ok results, and `commute_` reads the error from the type.

**Commutation under the world's choices** (step 13 review, G3). A call's failure is the world's choice for that call,
and so is a race's winner and where a loser is cancelled; with one list of them, the order of two steps would decide
which call fails, and `commute_i` would be false as stated. Where the world holds choices (`faults`, `races`),
`commute_i` gives each of its two steps its own lists, set as the step begins in either order (`modify`), and compares
the two orders' results and models' states, the choices left aside (`FrFlow.sameModels`). That suffices. Each step
reads only the choices it takes, from the front of its list, as in production each call's failure is its own; swapped
as above, each step keeps the choices it took. The reading on one list takes them too: the list is each step's part in
the reading's order, a step's part being what it took of its own list, padded with what a step reads where none is
left (no failure, of faults; `true`, of races) where it read past its own list's end, so that on the one list it takes
what it took and the next step starts at its own part. Every post is proven of every list. Today's form
(`w.faults = []`) is not used: it justified reordering only runs in which no call fails. Sharing's delivery's steps
commute so (`Lemmas.sends_commute`, `Lemmas.removals_commute`: each does what its faults alone decide, the mail
server's model a map by person as today's).
`p.changesNothing`, of a program declared to fail, says every model's state is as before
(`Worlds.unchanged(after, before)`, `Expr.Unchanged`; in Lean one equation per model's field, the faults left out),
and `===` between worlds is refused
where an operation may fail (`WorldsEqual`): it would compare the faults the calls took.

### 4.5 The front end: nodes, names, errors

A DSL node is `Node(head: Head, statement: Stating => Deferred[Statement])`: the head as written (id, sentence,
position, links), the statement built when elaborated, once the FrModel knows which Declarations change with the World
(`kb.Varying`, 2.2).

**A statement closed over its world** (owner §41, `node.Closing`). The world a statement holds in is a variable free
while it is written, read unnamed (`run.Worlds.current`, `VarId.world`: a Declaration, a define reading state) or
named (`Worlds.now`, `VarId.named`: `m.current`, `t.current`; `t.in(w)` substitutes `w` for the unnamed one), as is
each run it reads (`p.result`, `p.after`: a `RunNote`,
its outcome and world after `VarId.ran` of the run's IR). The statement's leading `forall`s keep their bodies
(`term.Forall`), so the closing opens them on free variables (`VarId.opened`), and, where what is below reads the world,
binds it right below them and each run right below it, by `Substituted`: `forall(request => … book(request).after …)`
is `∀ request, ∀ world, runs (book request) world (result, after) …`, the IR and Lean the explicit form had, the world's
binder named `world`. So `CallForms`, the guards (2.3), `Opened` and every analysis read it as before. A statement
reading no world is as written. A run is of the statement's leading variables (`Fault.RunInside` otherwise), from the
world it holds in. Closing refuses what would read otherwise than written (2.2): an `always` inside the formula
(`AlwaysInside`), a run read both ways (`ReadTwoWays`), the worlds after two runs (`AfterOfTwo`), an unnamed world read
beside a world after (`WorldUnnamed`), `isConstant` where no step keeps it (`ConstantInside`). While what changes with
the World is read off (`Stating.probing`), a statement is read with its leading `forall`s open, so its runs are read
as they are once closed (`Closing.opened`); `isConstant` is then stated per program (`analysis.Constancy`) once the
vocabulary is known, before validation. A run with both outcomes gives each side's post as written: the statement's
`fold` of the `Either` the run gives is that side's branch (`Sided`), not a `fold` of a constructor. Sharing's failing
runs, which step 13a printed so, moved twice in 13b (owner §41's closing printed the fold per side; this prints the
branch); their Lean is judged against today's when sharing is ported (step 13, its `PortSuite`).

`Source.valName`, read at compile time, names nodes, values, types and models: one name in code, reports and Lean.
Today's `Node` fields each have a place: `why` is the decision's reason, parents are edges, `post` and `op` are derived
from the formula, `file` and `at` are a `Sited(node, at: Span)`; `kept`, `runCheck`, `ideaSection` and `enforce` are
gone.

**An error waiting for its place.** A part built later is a `Deferred[A]` (an `Applicative`: errors accumulate,
declarations merge). An error found before its place is known is a `Fault`, carried in a term's notes or thrown as
`Failure(fault)`, and placed once as `ElabError(at: Site, fault: Fault)`.

### 4.6 Validation and resolution

`Validate(e: Elaborated): ValidatedNec[Problem, Valid]` returns every problem at once, one `Problem` case per thing
wrong: the graph (`DuplicateId`, `NoRoot`, `AboveItself`, `ParentOutside`, `DesignWithoutParent`, `UnderDesign`,
`PremiseNotAssumed`, `OutsideAsPart`, `OutsideClaimed`); the world outside (`PremiseMissing`, `PremiseNotNeeded`,
`AlwaysNotReached`); the vocabulary (`ReservedName`, `DeclaredTwice`,
`CodeOnlyInStatement`); values (`Undefined`, `DeclarationInCode`, `CodeWithoutClaim`, `RestsOnItself`); programs
(`RunOfNoDefinition`, `ErrorsDiffer`, `FailingDiffers`, `NeverFails`, `WorldsEqual`). A model's Lean namespace, its
name capitalized (`Stored`), counts among the declared names, so a model named as a declared type is
`DeclaredTwice`. `BoundaryUnchecked` is gone with the boundary (owner §36): a Definition with no meaning is
`Undefined`.

`Resolve(v: Valid): Resolved` computes once what each node uses, calls and rests on (`Callees`, `reliesOn`, which leaves
out a node's ancestors and descendants). `Scope` derives where an `always`, claimed or assumed, applies: the Definitions
and store programs whose values can hold a `T` (read off `Ty`), its makers, and the programs writing a store. Nothing is
exempt: a claim mentions only what it constrains.

### 4.7 Obligations derived from formulas

An obligation is a proposition in the logic of refinement before any Lean syntax (`proof.obligation.Prop`): claims
applied to their open terms, `Implies` with named hypotheses, `Iff`, `Both`, `Not`, `Forall`/`Exists` over open terms,
`ForEvery`/`ForSome` over named symbols, `Keeps`, `Makes`, `Starts`, `Inhabited`, `Commutes(c, opens)` (the commutation
and the open terms it is stated over). A formula is held as written (`Prop.Formula(Written[Expr])`); `TermTable`,
computed once, says what each declaration is applied to.

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

Of a node: `complete`, `impl`, `feasible`, `cover_<op>`, `made_<maker>`, `commute_i` (for each pair of steps at once:
`parTupled`, `parCollect`, `race`).
Tries, within a budget and one-sided (proven, they show something wrong): `needed_C`, `vacuous`, `restates`,
`restates_i_C`, `clash`, `unsat`, `idle`. A failed step is refuted when a node's one part fixes its result:
`StepRefutation` finds a case where the claim fails with that answer, and `RefutesModule` proves it. Of the whole
theory (`proof.whole`): `consistent_<i>`, `start_<node>`, `inhabited_<node>`, `satisfiable_<i>_<node>`, `example_<i>`.
Each obligation carries the sentence its Lean is documented with.

### 4.8 The Lean back end

The Lean AST (`proof.lean.ast`) says everything FrFlow generates; `LExpr` has no raw-text case. `LeanTerm` prints every
term, a define's body once as its `def`. Lowering gives only the structure around terms its Lean, handing each term to
`Printed`: `LowerProg` (a `do` block, names in `State[Naming, _]`), `LowerProp` (a `Writer` of open terms met),
`LowerObligation`, `LowerValue`, `LowerModels`, `LowerKeeps` (what `cover_` and `made_` declare), `LowerWitness`.
`Print` is a fold that decides nothing. `LeanProject` lays out node, root, vocabulary, whole-theory and refutation
modules. `proof.reading` and `proof.verdict` hold today's proof-file rules one case each, Lean's output and the judges.
The check judges the nodes level by level (`CheckPlan.byLevel`), each above its parts: a node's status reads only its
parts' (`CheckProgram.parts`), so where what the code relies on goes round (sharing's housekeeping and the claims on
what it calls), a second pass raises each node above its parts, and no node is judged before a part of it.
The Lean library gains only `frflow_witness`; examples are tries met by `frflow_auto`. FrFlow writes the project's
`lean/lakefile.toml` and `lean-toolchain`. A proof file is read only at `lean/Proofs/<Model>/<Node>.lean`, directly in
that directory; any other `.lean` under `lean/Proofs/` is a stray, which `review` lists and `check` refuses to run
beside (`StrayProofs`), since Lake would build it when imported. Judging fails closed: an obligation is Proven only when
its theorem's `#print axioms` line is there and within the allowed axioms, else Unchecked or Open, whole obligations
audited too. A check is current while its key holds, and the key includes FrFlow's Lean library (a hash of what Lean
reads of it) and the toolchain.

`CrmModulesSuite` prints four of crm's files byte for byte (`Boundaries.lean`, `Def_expireOnce.lean`,
`Def_expireOnce_run.lean`, `ExpiryJob/Spec.lean`); rooms' four golden files (`next/proof/src/test/resources/rooms/`)
state owner §21 and compile; step 11 regenerates them for owner §25 (one type, `Booking`). Constants are printed typed
at their root (2.9), so the goldens are no longer the spike's text verbatim; step 11 regenerates `lean-spike/Dump.lean`
and rechecks `Proofs.lean`. Today's Lean is a reference, not a constraint (owner §2, D).

### 4.9 Testing before production

Property-based testing stays in full and carries every check the running service made:

- **Plain code against every claim mentioning its Definition** (`PropertyTests`): inputs drawn, the values the code
  reads made by `eval.run.Wiring`, the call judged by `CallCheck` (the post, and each `always[T]` of the call's values,
  `Made`) or the claim evaluated whole; the first failure shrunk, saved, replayed first; coverage of what each case
  reaches (each implication's premise holding, each side of an `or`, each condition both ways, each arm of a match, each
  list or option a quantifier ranges over not empty; in model tests each operation called and each branch of the model's
  steps), every target starting at zero, so one no case reached is said. A report counts the cases asked and tried
  (`Count`): a case that cannot be drawn is not tried, and the shortfall is said. A claim with no Scala value is "not
  checked" (`Outcome.NotChecked`), never a failure, and nothing is shrunk, saved or replayed for it.
- **`Wiring`** makes a call's values explicitly (defines, the meanings of what it calls, the values given), for
  examples, tests and production's `knowledge.code(d)(bindings*)` alike.
- **An adapter** against its assumption's formula and its model (`ModelTests`, 3.8).
- **Interleavings** of a concurrent program on the adapters, over the recorded `Prog` Lean proves, deterministic under
  `TestControl`; production's concurrency on its own (`RunningSuite`).
- **The step refutation** and **the witness search** (`testing.search`).

Every value drawn by its type meets each `always[T]` of the type and of each value nested in it, an example's seed
values included (`Respecting`, `DrawnSuite`); a drawn world takes faults where an operation may fail and races' winners
where a program races. A run is a function of its seed and the code. A report carries notes (`Note`): what a given
generator made (`Given`), the examples' values it never made (`NeverMade`), and a call with nothing to vary
(`NothingToVary`).

### 4.10 Views and the API

`View(nodes, roots, whole, overview, warnings, gone)` is derived once (`api.derive`, `private[api]` as `api.shell` is);
front ends never see `Analysis`. `WholeView(groups, starts, possible, examples)` (`api.view.whole`) holds the
consistency groups, each store's start (`StartView`), what is shown possible, and the examples.
`NodeView(id, says, place, proof, code, review)` has one group per concept: `Says` holds the formula, `checking` and
the decision's reason; `ProofView(state, results, findings, authored, unproven)`;
`ReviewView(version, standing, decisions, waitsFor, notMechanical, moves)`. A node's `diff` is a typed `NodeDiff`.
`api.node.lean` and `api.node.tests` mirror what Lean and the tests found, so front ends depend on no lower module's
types for them. `Overview` is `Tally[K]` fields, a commutative monoid, and `complete`, the CI gate: there are nodes,
none is gone, each is accepted with nothing of it unproven, each store's start is proven, and every consistency group
is proven (2.8). What an operation cannot
go on from is raised as a `Stop` (`Invalid`, `NoLean`, `NoKey`, a file that does not read); what the developer should
know is a `Warning` (`NotCounted(node, decision, why)`, `BaseNotCommitted`, `StartNotProven`, `Ungoverned`, …). The
API is three algebras in `FrFlowApi[F]`:

| Algebra | Operations |
|---|---|
| `Reading` | `view`, `diff(node)`, `find(words)`, `modelFingerprint` |
| `Deciding` | `developer(as)`, `preview(command, by)`, `decide(command, by)`, `rebase(by)` |
| `Proving` | `render`, `status`, `snapshot`, `check(only): Stream[F, CheckEvent]`, `ci`, `scaffold(node)` |

`Deciding` answers `Decided`, `Rebased` or a `Refusal`; an acceptance is decided on what this process checked and
tested afresh (6). `scaffold` answers `Scaffolded` (`Written`, `NothingToAdd`, `EndNotFound`). A project is
`Project(model, examples, adapters, sources, library)`. Its interpreters: `FrFlowApi.make(p, root, env)`, a `Resource`
holding the ledger's lock and one `lake` build at a time, run as `env` says (`FRFLOW_LAKE`, `FRFLOW_KEY`,
`FRFLOW_SEED`, `FRFLOW_AS`, and `HOME` for the default key); and `FrFlowApi.inMemory(p, files, decider, lean)`, the one
the front ends are tested on, its Lean a `Lean.Proving(failing, shown)` or `Lean.Absent`. `FrFlowApi.firstDecider`
writes the first deciders' list (`Listed`).

A project's main object is a `FrFlowProject`: its project, its directory, and the layers on top (`Extension`). A layer
sees a `Host(reading, developer, directory, env)`: reading and who the developer is, never deciding or proving. The
command line (`cli`) has today's commands and adds `rebase` (the owner accepts the ledger as it reads now as where its
committed history starts), `deciders` (the first list, signed by the developer's key) and `export` (the snapshot);
`--json` on `status` and `check` prints the snapshot. The web view (`web`) binds `127.0.0.1` only; its `Gate` admits a
request only with the session's token (in a header, or in the link for the page and its scripts), from no other
page's origin, a write only as JSON, and refuses deciding once the model's fingerprint moves from what the process
compiled. The agent layer (`agent`) never decides: its commands and routes read the view and ask.

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
| `dsl` | core | the user's syntax, elaboration, `Term[A]`, `Flow`, `StateModel`, macros |
| `proof` | core | obligations, the Lean AST, the term printer, lowering, layout, judges |
| `eval` | dsl, cats-effect-kernel, -std | the term evaluator, `Running`, `CallCheck`, `Wiring`, `ExampleRun`, `FlowInterpreter` |
| `testing` | eval, cats-effect, sbt test-interface | `Draw`, `Respecting`, `PropertyTests`, `ModelTests`, `Interleavings`, searches |
| `decision` | core (names, `graph.Walk`, `spec.NodeKind`) | content, ledger, deciders, payload, review, rules |
| `wire` | proof, decision, testing, circe | the snapshot by kind; codecs of ledger, deciders, checks, tests |
| `project` | proof, testing, decision, wire, cats-effect, fs2 | algebras, programs, `Analysis`, contents, fingerprints |
| `api` | project | `Reading`, `Deciding`, `Proving`, `FrFlowApi`, views |
| `cli`, `web`, `agent` | api (agent also cli, web) | front ends and the agent layer |

Each module has its own top package (`frflow.core`, …), so `private[core]` is a real boundary. The planned code has
the first nine; `cli`, `web` and `agent` keep their structure and are rebuilt on the new API. Serialization points
outward: only the shell depends on `wire`. Five edges are between tests only (`test->test`): `next-proof` on
`next-core`'s fixtures (`next-core % "compile->compile;test->test"`), `next-eval` on `next-proof`'s, `next-testing` on
`next-eval`'s, `next-project` on `next-testing`'s and `next-api` on `next-project`'s; production `eval` never sees
`proof`. The agent depends on `cli` and `web`; `web` does not depend on `cli`. Front ends see `api.view` and `api.node`
values, and the core, dsl, decision and eval values those hold (`NodeId`, `Decision`, `Refusal`, `Command`, `Standing`,
`Unproven`, `Problem`, `Ty`, `Value`, …), never `project`, `proof`, `testing`, `wire`, `api.derive` or `api.shell`:
each front end's `ArchitectureSuite` checks it on the sources and on the compiled classes, since depending on `api` puts
those on the classpath, and the agent's also forbids every deciding call. Production code depends on `eval` (and through
it `dsl`, `core`) and never on Lean, the ledger, the tests or the CLI.

Planned so far (files / lines): `core` 146 / 3,213, `dsl` 69 / 2,178, `proof` 79 / 2,058, `eval` 26 / 727, `testing`
22 / 428, `decision` 42 / 694, `wire` 14 / 184, `project` 25 / 621, `api` 27 / 381. With the ports written and `cli`,
`web` and `agent` rebuilt, the projection is about 13,700 lines in about 570 files, against today's 12,008 in 347:
about 12% more, consistency and vacuity among it, in smaller files, with no type over six fields. Built, after step
12b (files / non-blank lines): `core` 150 / 3,757, `dsl` 74 / 2,498, `proof` 108 / 3,635, `eval` 35 / 1,078,
`testing` 58 / 1,449, `decision` 47 / 794, `wire` 38 / 975, `project` 66 / 2,218, `api` 82 / 1,380, `cli` 41 / 1,695,
`web` 11 / 404, `agent` 26 / 533: 20,416 lines in 736 files, about half again the projection, most of it in what the
ports needed (the rules' obligations and their selection in `core` and `proof`) and in the shell.

## 6. Data: decisions, deciders, ledgers, fingerprints

**Content.** `Content(fields: List[(String, FieldValue)])` is a node as the developer decides it: named fields in a
fixed order, a canonical print, `hash` (whitespace runs ignored) and `ref` (the exact form a signature covers, a full
SHA-256, as a ledger entry's ref is). One form (`Contents.of`): `kind`, `parents`, `parts`, `assumes`, `statement`,
`formula`, `written`, `vocabulary`, `checking`, `governs`, `call`, `replaces`, `reliance`, `failure`, `implementation`,
`model`, `implementations`. No `why`, source excerpt or `idea`. `formula` is the meaning: the elaborated formula as Lean
is given it, variables named by the order they are bound, then each define it calls, so a helper's body that changes
moves it and wording the Scala differently does not; `written` is the Scala as written, shown only (`Meaning` leaves it
out). `Meaning.own` (cause `self`) leaves out `parts` and `parents`, but a design keeps its `parents`.

**Ledger and review.** The `Ledger` is append-only; review states are a fold of it over the current graph, parents
first (`Standings`). A node returns for a cause: `self`, `above` (unless only words moved, `Reworded.only`), `parts`,
`code`, `revisit`, `merged`, a parent rejected, and, for a claim of `always` about a store, a program newly derived to
change the store (`writer`, naming it; owner §31); `Cause.movedUnderCode` lets the CLI say a failing case as the claim's
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
final case class Deciders(entries: List[Decider], after: Option[String], seal: Option[Seal]):
  def allows(name: String, key: String): Boolean = entries.exists(d => d.name == name && d.key == key)
```

The first version is signed by its first entry, each later one by a key the version before listed, naming that version
(`after`), so replaying an old list breaks the chain and cannot restore a removed decider. FrFlow reads only committed
versions (`Git`) and takes the last when each follows the one before. A decision counts only when its key is listed
under its decider's name and the signature verifies; `DecideProgram` refuses an unlisted key before any rule
(`Refusal.NotADecider`). `init` writes the first list. A version with no seal follows none. `Payload.of(id, d)` frames
each field (its length, a colon, then itself: `Framed`): the node id, action, by, at, reason, the rejected ids after
their count, chain, code fingerprint, commit, after and `content.ref`, so no reason or id can make two decisions' bytes
the same.

**What the agent can write, and what the key protects.** An agent writes the project's files and commits: the model and
its code, adapters and layers, the proofs, and every record under `.frflow/` (`checks.json`, `tests.json`,
`counterexamples.json`, the ledger) and Lake's `lean/.lake`. Only the owner's key makes a decision count, a deciders'
list follow, or a ledger base take. So the agent's process must not be able to read the key (another OS user or a
sandbox; `FRFLOW_KEY` not in its environment). FrFlow cannot protect it otherwise: every command and `serve` the owner
runs executes the project's Scala (the model, adapters, layers), which the agent writes, in the process that holds the
key; the owner decides in a checkout whose Scala he has read. An acceptance (`Accept`, `Confirm`) is decided on a check
and test this process makes afresh, never on the records on disk alone; Lake's `.lake` is trusted until step 15, whose
run starts from a clean `.lake` and runs `lean4checker --fresh`. The anchor is the history as pushed.

**Counting.** `Counted` holds the decisions that count and the others, each with why (`Uncounted`: `NoDeciders`,
`NotListed`, `NotVerified`, `Rewritten`, `Unreadable`). Each node's history in every committed version of the ledger
must be where its history in the next version, and in the working ledger, starts; a node whose committed history was
taken out or changed is `Rewritten`, and a committed version that does not read makes every decision `Unreadable`.
Deciding is refused while any node is either (`Refusal.Rewritten`). A decision taken stores only what it added
(`Counted.stored`), the uncounted decisions kept; `.frflow/ledger.lock` serializes writers across processes.

**The ledger base.** An unreadable committed ledger, a committed deletion the owner accepts, or a merge of two branches'
decisions would lock deciding for good. `.frflow/ledger-base`, committed, is the owner's way out: each version names the
full SHA-256 of the ledger text it accepts and the version before it (`after`), signed by a key some committed deciders'
list held, the newest by a key listed now (`LedgerBase.committed`). The history is counted from the commit that made the
base, when that commit's ledger text has the base's hash (`LedgerBase.from`); every later committed version still
counts, so a text committed again rewrites nothing unseen. A base over a text never committed does not take, and
`status` warns (`Warning.BaseNotCommitted`). `rebase` writes it, refused unless the key is listed under the name
(`Deciding.rebase`). A base never makes an unsigned or unlisted decision count.

**Fingerprints.** `CodeFingerprints.of(files)` hashes a design's governed files, sorted, as the simple lexer reads
them (owner §2, F): comments blanked, blank lines and trailing spaces dropped, indentation kept, runs of spaces
collapsed. A change of meaning always moves it; comment and spacing edits do not; a few harmless edits do (`f(/*a*/x)`
to `f(x)`).

**Code in a file that holds nodes** (owner §38). The expression given to `implementTested` is part of the node's
content already (its `implementation` line); the definitions it refers to are fingerprinted wherever they are written.
A file holding no node or attached code is governed whole, as before. A file holding nodes is governed only by the
spans of the definitions referred to: `SourceFiles` records each referred symbol's file and start, and the lexer takes
its span, from that line to the next line at the same or a lower indentation, adding the spans of the same file's
top-level definitions a span names until nothing new is added. So editing a node beside the code brings nothing back,
and editing the code does: keycloak's `introspection`, written in `Introspection.scala` beside four nodes, brings
`introspectAnswers` back with `Cause.Code`.

**Exports.** The snapshot (`.frflow/kb.json`) is `wire`'s own rows by kind, made by one mapping (`Rows`), printed by
`--json` and read by no FrFlow module; `wire` also has the codecs of the ledger, deciders, the ledger base,
`checks.json` (`{checks, whole}`: each node's check, and the whole theory's) and `tests.json` (each report with its
notes), and the committed `counterexamples.json`. Each file starts with its `version`; the ledger stores each content
once, by its ref; a seed is written as a decimal string in every file, so a reader that rounds numbers (JavaScript, jq)
keeps it.

## 7. Errors and effects

### 7.1 Errors

| Where | Type | Channel |
|---|---|---|
| elaboration | `ElabError(at: Site, fault: Fault)` | `ValidatedNec`, all collected |
| structure | `analysis.Problem` | `ValidatedNec`, all collected |
| either, at the shell | `Problems.NotElaborated`, `Invalid` | raised in `F` (`NoStackTrace`) |
| evaluation | `EvalError` (`Quantified`, `Unbound`, `NoDefine`, `NoCase`, …) | `Either` |
| a program run in Scala | `FlowError` (`NotEvaluated`, `NoModel`, `NoOperation`) | raised in `F` |
| a program's own error, in production | `Raised(error, ty)`, its cause kept | raised in `F` |
| decisions | `Refusal`, e.g. `NotADecider(name)` | `Either`; the caller goes on |
| a check | `Finding` cases (`Refuted`, `DisallowedAxioms`, …) in `Judged`, `NodeCheck` | data |
| the theory as a whole | "consistency not proven" (a failure: the proof is red), "not shown", "not checked" | data |
| tests | `TestReport`, `Failure(inputs, broke: Broken, …)`, `Difference` | data |
| plain code, a running program | `NotEvaluated(EvalError)` | thrown |
| `knowledge.code`, `running`: no meaning, or no elaborated base | `IllegalArgumentException` (`CodeSyntax`) | thrown |
| the shell (no Lean, unknown node) | `FrFlowError` | raised in `F` |
| FrFlow bugs | `IllegalStateException`, "FrFlow bug" | where types rule the case out |

`Fault` has thirteen cases (`NoType`, `NotData`, `NoField`, `NotAClaim`, `ProgramMentioned`, `MeantWhereWritten`, …).
`Broken.Always` is an `always[T]` a call's value breaks. Production code has no `Either` to return, so plain code
evaluating a term with no Scala value throws `NotEvaluated`; inside the evaluator `app` turns it back into `Left`. A
program called as code (`knowledge.code(program)`, `d.fn`) gives `NotEvaluated(Steps)`: a program runs through
`knowledge.running` and lifted adapters. Text for the developer is made only in `cli` and `web`.

### 7.2 Effects: where F[_] is used, and why

`core`, `proof`, `decision`, `Evaluate` and the generators have no effect type; `dsl`'s `Flow[R]` is data (its steps)
and runs nothing. Each `F[_]` pays for itself:

| Algebra or program | Why over `F[_]` | Second interpreter or law |
|---|---|---|
| `ProjectFiles[F]` | the checker tested without a disk | in memory; a read after a write gives it |
| `Lake[F]` (`Resource`) | planning and judges tested without Lean | scripted, answering by module |
| `Git[F]` | decision tests without a repository | in memory |
| `LedgerStore[F]` (`Resource`, the lock) | the CLI and web view may decide at once | in memory; stores only on `Right`, serialized |
| `KeyRing[F]` | tests never touch the developer's key | a key in memory; deciders read from `Git` |
| `RunCode[F]` | running the developer's code, which may block or throw | in the effect's own steps; live on the blocking pool |
| `ReadInputs`, `RunScala`, `CheckProgram`, `NodeChecker`, `DecideProgram` | programs | ask only `Monad`, `Parallel`, `Clock`, `RunCode` |
| `FrFlowApi[F]` | the CLI, web and agent suites | in memory; `preview` shows what `decide` records |
| `Running[F]` | a program's steps folded into the developer's effect | `FlowInterpreter` on the models; they agree |

Concrete `IO` appears only in the web server, the CLI's `main` and the terminal; in production the developer picks
`F`.

### 7.3 State and casts

State, each piece named: `FrModel.elaborated` (a `lazy val`), `Running`'s lock, and a recording's reading's
`State`. Atomics and locks are allowed only in `eval.Running` and `FlowInterpreter.concurrent`, `ThreadLocal` nowhere.
Casts are in twenty-five files, sixty-seven in all (step 13b's count): in `core`, `Guards`, `AtValue`, `Defining`,
`Conditions`, `Substituted` and `Written` (`term`, `retyped`); in `dsl`, `Term.bound`, `Definition.called`,
`ValuesSyntax.apply`, `ReadRecording`, `kb.Calls` and `kb.Tested` (the `call` an operation's Scala is reached by),
`Declaration.applied` (a Declaration applied, typed by its extension), `shape.Defines.in` and `shape.Worldly` (a
program's and a world-reading define's inputs), and `node.Closing` (a statement closed over its world and runs); in
`proof`, `Calls`, `CallSites`, `Making` and `Keeping`; in `eval`, `Fn`, `Evaluate`, `Running` (a program's steps
folded, each case's result at its case's type) and `flow.Bound`; in `testing`, `ModelTests`. Each is
typed by what was read before it: the transformers that build terms from a type known only at run time (a guard, a
call site, a witness) work at `T[Any]` and cast to the term's type. Neither the printer (`LeanTerm`) nor `ToExpr`
casts; `Evaluate` casts where it reads untyped given values (`Fn.as`); no unchecked type test is left outside `Fn`.

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
| a store's model | a `StateModel` giving each operation's meaning; its Scala tested against it (owner §36) |
| a boundary, its trait, `behavesAs`, `BoundaryUnchecked` | none: operations are Definitions; the generated-run test and `stored.onlyCodeChanges`; `Undefined` (owner §36) |
| definition node (`authorized := …`) | a claim of one equation, or a `define` |
| `Param`, `Operation`, `Open` | `Declaration`, `Definition` |
| `.expects(statement)(consequence)` | a claim the expecting claim refines |
| `.failsChangingNothing[E]`, `.onFailure` on a node | part of the run in the formula |
| `.keeps`, `.exempt`; relations of answers | derived (`Scope`); a claim over the Definitions it relates |
| `.examples`, `allows`/`forbids`, `bind`, `eval_i`/`probe_j` | examples as tests (2.10) |
| two definitions of one term | two claims, one `.replaces` the other |
| `==>`, the Boolean `fold`, `before(stored)` | `implies`, `when(…)(…).otherwise(…)`, `stored.in(before)` |
| assumptions on what calls a Definition | a type for what comes from outside, with an assumption of `always` on it (2.6) |
| `stored.writtenOnlyBy(p)`, `WriterNotListed` | derived: the programs calling an operation whose meaning changes the state; `stored.onlyCodeChanges` says nothing outside the code changes it (owner §31, §36) |
| `stored.changedOneRunAtATime` | `stored.atomic`, on the model (owner §32, §36) |

**Everything else**: `why` on nodes (the examples' `why` texts are offered as the reasons of their first decisions);
`IDEA.md`, idea sections and numbered questions (owner §1: the purpose is stated by the root statements; a README is
prose FrFlow does not track); ambient state (`Param.value`, `Bindings`, `Watch`, `Building`, the `LeanType.known`
registry, the fresh-variable counter, reflection on lambdas and bytecode; the examples' 34 `p.value` become `env(d)`);
today's `Flow` values and `Flow.effect`; content forms, `confirm --rebind`, `Retired` ids, text fingerprints and filed
keys as authority; the compiled-define memo.

## 9. The rebuild plan

The new FrFlow is built beside today's in this repository and replaces it once every example runs on it. Today's
modules are not changed, but for step 0, which records their outputs.

**Frozen** (owner §29). Today's library is frozen until step 14 except for bug fixes: `modules/*`, `examples/*` and the
README's code. Every further change to what FrFlow is or how an example reads goes through `next/*` and this design.
The three changes today's library made after approval (owner §25) are the last; step 11 carries them into `next/`.

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
| 3b | core and proof: a program's error type (4.4); `impl` over every part (2.7) | a failing writer's `cover_`, a `.failing` `impl`, a crm-shaped run claim |
| 4 | `next/eval`: `Evaluate`, `Running`, `CallCheck`, `Wiring`, `FlowInterpreter` | `TermLawsSuite`, `RunningSuite`, recording agrees with running |
| 5 | `next/testing`: generators, `PropertyTests`, `ModelTests`, searches, examples' runner | ported suites with seeds, `Gen` laws, `SmallSuite` |
| 6 | `next/decision`: content, ledger, `Deciders`, review, rules | ported decide and standing suites, `DecidersSuite` |
| 7 | `next/wire`: rows and codecs | a round trip per file |
| 8 | `next/project`: algebras with in-memory interpreters, programs, `Analysis` | `check`'s suites over the in-memory interpreters |
| 9 | `next/api`: the three algebras, views, `FrFlowApi.inMemory` | `api`'s suites |
| 10 | `next/cli`, `next/web`, `next/agent`; `init` writes the deciders' list | `cli`'s and `agent`'s suites, a web smoke test |
| 11 | the rules of 2.3 to 2.8 that today's rooms needs (below); rooms ported as section 3 writes it; the README walk-through rewritten | a suite per rule; rooms' suites, the Lean spike, `PortSuite`, `WalkthroughSuite` |
| 11b | Boundary removed (owner §36); rooms re-ported; README draft redone | rooms' suites, `PortSuite`, `WalkthroughSuite`, the Lean spike; no `Boundary` left in `next/` |
| 12 | `made_` at the call, the fingerprint of code beside nodes; auth, then keycloak, then crm ported | each `PortSuite` and its seeded bugs |
| 13 | sharing ported, with the kept combinators' uses; its failing runs' Lean judged (4.5) | its `PortSuite`, fault sweep and interleavings |
| 14 | today's modules deleted, `next/*` moved, docs and skills rewritten | the architecture test at target, size baseline at zero |
| 15 | the owner decides each example's ledger with his key | `confirm` for the mechanical nodes; nothing earlier counts |

Step 2 also writes every node of the five examples in the three kinds before any port, and keeps the compile-time spike
in the build. Step 3b's run claim in Lean is a crm-shaped fixture (`Failing.file`): crm's own `runExpiry` cannot fail in
the new DSL. Step 5 makes drawn values meet their fields' rules (`DrawnSuite`). Step 11 first carries into `next/`
what today's library learned after this design was approved (owner §25): a claim of `always` below the statement it
serves is a rule, no part of the step, and so is an assumption of `always` (2.4); a claim at the bottom mentioning a
Declaration says what it is, with no `impl` and no premise list, its group joined through the code standing in it and
solved in order (2.7, 2.8); `start_` and `inhabited_` asked of an assumption of `always` too (2.3, 2.9); `show` and
review listing rules apart from parts (2.4); consistency gating the proof: a group not proven is red, for the whole
model and for every statement proven from parts over a Declaration (2.8, owner §28); and every boundary covered code
calls having a model or an assumption (4.4, owner §30); the programs changing a store derived, `writtenOnlyBy` gone,
and `atomic` said of the boundary (2.6, owner §31, §32). None needs a new kind of node or value, a quantifier or a
second name.

Step 11b removes the boundary (owner §36), before any outside system is ported: `Boundary`, its trait as interface,
`BoundaryOps`, `behavesAs`, `BoundaryUnchecked`, and today's `Clock` trait go; an operation on a state is a Definition
given its Lean meaning by a `StateModel` and its Scala by `implementTested(ops*)(start, observe)(calls)`;
`onlyCodeChanges`, `initially` and `atomic` are said of the model; the clock is two Definitions with their model. Lean
sees what it saw (each operation runs on its model's field of the World), so rooms' Lean changes only in names. Rooms
is re-ported as section 3 writes it, its goldens and `WalkthroughSuite` texts follow, and the README's rooms draft is
redone and goes through its readers again (owner §3). The work list is the step's impact list.

Step 12 builds `made_<code>_call_<i>` (2.3, owner §37) and the fingerprint of code beside nodes (6, owner §38), each
with its suite: a crm-shaped fixture whose rule "one row per key" a seeded expiry job breaks at its `storeAbout` call,
and the `Introspection.scala` case. Then auth, keycloak and crm are ported (owner §40):
- Auth: its `Param`s become Declarations and Definitions (`grants`, `sessions` provided, `admit` tested), `sessions` a
  list with the assumption `tokensIssuedOnce`, and `Server` calls `knowledge.code(admit)(…)`.
- Keycloak: it loses its `checkedBy`; its store's `lookup` and `record` are plain Scala known by their assumptions
  (`sessionLookup`, `storeKeepsState`); the claim on `introspect` is the node `introspectAnswers`.
- Crm: its database's `load`, `storeAbout` and `logEvent` are Definitions with the model `databaseModel`, its expiry
  job gains its `ifM`, its tables hold one row per key (`always[CrmStore]`), `noCrossTenantRead` is a root over two
  Definitions, and `acmeNeverSeesGlobex` is an example test.

The consistency groups of keycloak's store and crm's search are proven by a hand-written `consistent_<i>` each, with
today's `storedSession` and `storedMatching` as witnesses; an agent may write them, Lean checks them, and the developer
decides the nodes as usual (2.8, owner §28, §39).

In step 13, sharing uses `timeout`,
`race`, `bracket` and `parTupled`, each under a proven claim. Step 13d builds time as Cats Effect models it (owner §47,
"Time" in 4.4): the clock's `elapse`, schedules, ticks, waits at once read as two points, rules over several models;
crm's clock and sharing's run are the World's (§45 D done). Step 14 rewrites `docs/USAGE.md`, `docs/DAG.md`,
`docs/index.html` and the frflow and scala-fp skills.

**Stubs by step** (40 `???`, `review.md` lists the first ones the owner will meet): step 2, `derives BoundaryOps`, and
`Flow`'s `collect`, `fold`, `parCollect` and `attempt` (not yet written at all); 3, `feasible`, `commutes`, `made_` of a
program's result, guards inside maps and sets (refused until then, `AlwaysNotReached`), module layouts, a few
`LowerProg` steps; 3b, a program's error type, `impl` over every part, `PartNotCalled` dropped; 4's (`FlowInterpreter`'s
loops and errors, `Literals` of maps and sets, `CodeSyntax.code`) and 5's (`ModelTests.of`, derived generators,
shrinking, the examples' runner) are filled in `next/`, but `StepRefutation.candidate`, which moves to 8; 6's three
review functions, 8's (the port interpreters, `NodeChecker`, the lexer's passes, `StepRefutation.candidate`) and 9's
(`FrFlowApi.make`, `Views.tree`, `Views.inbox`) are filled in `next/` too.

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
| two FrFlows in one build during the rebuild | certain | today's library frozen but for bug fixes (owner §29); every change goes through `next/` |
| tagless programs read differently (sharing's 3,247 lines) | medium | sharing last, after each combinator's recording test |
| compile time: rooms 1.3 times slower from clean (10.3) | medium | one helper per operator, macros only where written, measured per port |
| a derivation at every use passes the JVM's limits | seen, fixed | `LeanType` derived once per type; sharing's file compiles in every build |
| renaming a val renames its node | certain | `review` shows a gone node and a new one with the same content |
| a claim meant as a call is tested whole | low | `show` says how each claim is checked |
| a claim with no Scala value is not tested (rooms' root words) | certain | `show` and `status` say so; rooms proves its one from its parts |
| an `always` rule with no Scala value cannot be drawn (rooms' `neverOverlap`) | medium | state it in evaluable words and prove the link |
| a data type no statement mentions is not drawn | low | it is not in the vocabulary: mention it, or give its generator |
| no witness derived for a sound group | medium | the proof is red until an equation, value or proof is added (owner §28) |
| the outside facts are many to write (rooms: four) | certain | each is one sentence; a missing one is named with what to say |
| an outside vocabulary lacks a native interpreter | low | it runs through its meaning in the core, a law tying the two |
| a bug only production data shows | certain in principle | the owner's decision; seeds include the examples' worlds |
| the examples' decisions are lost | certain | old `why` texts offered as reasons; `confirm` batches |
| the macros meet a case the examples lack | medium | `ElabError`s name the site; `StateModel` reading tested per example |
| rewriting 5,176 lines of tests lets a case slip | medium | ported suites keep case names; a step lists what it drops |

### 10.2 Open questions

In order of value; none blocks a step.

- **Settled (owner §46): the spelling of a program that can fail.** `Flow[R]` and `Flow[E, R]` cannot both be types,
  so the error is declared on the Definition, `.failsWith[E]` (2.2); `.current` names the world before a run.
- **Step 11: the README's forms.** `implementTested`'s `start` and `observe` could say their roles (`startFrom`,
  `readBack`); introduce `World` where first used; warn when a node reached by an edge is missing from the `FrModel`
  list, or collect the list. (Settled by today's rooms: a `RoomBookings` names its room, `bookingsOfTheRoom` says so,
  and `Calendar` grants a request for another room; the names are `inRoom`, `add`, `storedBookings`, `nothingElseWrites`
  and `startsEmpty`, step 11b's.)
- **Steps 1 and 11: rules without a Scala value.** Today's rooms states `roomBookingsApart` over moments (`apart`);
  the port keeps `noOverlap`, since drawn values are judged by it (2.3). Make the limit a validation message, not only
  a risk.
- **Long premise lists (the owner's call).** The store's three facts recur on every claim about the store; an
  assumption could group them, if the owner agrees, still one edge and one kind.
- **The double reading of `always`** (of a type, of a store) is kept as one word, read as "every value the covered
  code can produce" (owner §19); asynchrony is out of scope (owner §17).
- **Settled (owner §30, §36, §37): a value handed to code FrFlow cannot see.** There is no boundary: every Definition
  has a meaning (`Undefined` otherwise), and what proven code hands to plain Scala meets the rules on its type
  (`made_<code>_call_<i>`, 2.3), so a value built inline and passed on never goes unchecked.

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

1. **The module graph is in `build.sbt` only**; a new module or edge is approved first (the test-only edges of 5 among
   them).
2. **`ArchitectureSuite`** (munit, about 150 lines) scans imports and package clauses and fails on: a package edge not
   in `project/architecture.conf`; a package cycle in a module; `private[frflow]`; `ThreadLocal`; `cats.effect`,
   `io.circe`, `java.nio.file.Files`, `scala.util.Random` or `System.getenv` in `core`, `dsl`, `proof` or `decision`;
   atomics, `Mutex` or `synchronized` outside `eval.Running` and `FlowInterpreter`.
3. **scalafix `DisableSyntax`** on `core`, `proof`, `eval`, `decision`, `dsl`: no `null` (but `dsl.node.Parent.of`), no
   `var` in classes, no `throw` (but "FrFlow bug" sites, `Failure(fault)` in `Elab`, `ReadRecording`, `Term.select`,
   `CodeSyntax`'s refusals, and `NotEvaluated` where 7.1 says), no `asInstanceOf` outside 7.3's places, no
   `isInstanceOf`, no `@unchecked` outside `eval.Fn`.
4. **Size budgets** in CI against a committed baseline: a change may not add a violation. The five- and six-input
   `apply` forms of `Declaration` and `Definition` are an accepted exception to the four-parameter limit: Scala cannot
   shorten them.
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
| Derived view | `api/derive/NodeViews.scala` |
| Errors as cases | `decision/rules/Refusal.scala` |

## Appendix A. The owner's decisions

The decisions are in `owner-decisions.md`; the right column says where this document applies each.

| § | Decision | Where |
|---|---|---|
| 1 | No `IDEA.md` or numbered questions; the README is prose | 8 |
| 2 A, 5 | Terms concrete for the user, tagless-final inside | 4.2 |
| 2 B | No ambient state | 2.2, 4.2, 7.3 |
| 2 C | Tagless programs (the boundaries removed by §36) | 4.4 |
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
| 19 | One word `always` for both forms | 2.3, 10.2 |
| 20 | The design approved; the rebuild started | 9 |
| 21 | Statements about values only; what comes from outside an assumption of `always` on its type | 2.6, 3 |
| 22 | crm's purpose is the root; its expectations are roots of their own | 2.5 |
| 23 | The README's short core and its pass rule | outside this design |
| 24 | `KnowledgeBase` renamed `FrModel` | throughout |
| 25 | Rooms keeps one type, `Booking`; an `always` assumption is a rule; who lists it | 2.4, 2.6, 3 |
| 26 | `generating` is called `withGenerator` | 3.7 |
| 27 | The design before step 11: rules below a statement, Declarations' meanings, who lists an assumption | 2.3 to 2.9, 3, 9 |
| 28 | Consistency gates the proof | 2.8, 4.10, 7.1, 9 |
| 29 | Today's library frozen but for bug fixes | 9 |
| 30 | Every boundary has a model or an assumption (its boundary wording superseded by §36); `made_` at the call | 2.3, 4.4, 10.2 |
| 31 | `writtenOnlyBy` dropped: the programs changing a store derived; nothing outside changes it, now `onlyCodeChanges` (§36) | 2.3, 2.6, 3, 6, 8 |
| 32 | `changedOneRunAtATime` is `atomic`, on the boundary, now on the model (§36) | 2.6, 3, 8 |
| 33 | One World, kept local: a statement takes only the stores it reads; a new store brings nothing unrelated back | 2.3, 3.2, 9 |
| 34 | A run is written with `.from` (and `.failing`); `.answer`/`.after` not carried (superseded by §41) | 2.7, 3, 8 |
| 35 | A boundary has a Model: `StateModel` or `AssumedModel` (superseded by §36) | 2.2, 4.4 |
| 36 | No `Boundary`: what FrFlow cannot see is a Definition given plain Scala; a `StateModel` gives a stateful one's meaning; operations are separate Definitions ("A for now") | 2.2, 2.6, 3, 4.4, 8, 9 |
| 37 | `made_` at the call, every call, a Lean obligation only | 2.3, 4.4, 10.2 |
| 38 | Only the definitions code refers to are fingerprinted in a file holding nodes | 6 |
| 39 | Hand-written consistency proofs; agents may write them | 2.8, 9 |
| 40 | The ports' decisions: crm's row rule, crm's roots, auth's `tokensIssuedOnce`, `introspectAnswers` | 9 |
| 41 | The World implicit in statements; `.result`, `.after` replace `.from` | 2.2, 2.7, 3, 4.5 |
| 42 | One `Flow`: a program is a `Flow[R]`, a `for` comprehension; no `Program` | 3.2, 4.4, 7.2 |
| 43 | No marker for what changes: read off the statements and the defines' bodies; `d.isConstant` | 2.2, 3.4 |
| 44 | `isConstant` on any value: no next step changes it, one equation per program | 2.2, 4.2, 4.5 |
| 45 | One `isConstant`; error in the type (§46); no worldly rule; D at step 13; safety only | 2.2, 2.7, 10.2 |
| 46 | A program that can fail: `.failsWith[E]` on its Definition, `p.result` an `Either`; `.current` | 2.2, 2.7, 4.4 |
| 47 | Time as Cats Effect models it: the clock's time the World's, `elapse` the world's step, ticks, schedules | 2.2, 2.6, 4.4 ("Time") |
| 48 | Auth's tables stay provided | 2.2 |

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
| P4. `FrModel` a god object | `Theory` (five fields), `Resolved`, `testing.Settings` (4.1) |
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

