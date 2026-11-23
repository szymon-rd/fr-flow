# Scala as trees of effects: the representation and the translation

This page is the design of one representation of compiled Scala for the prover, and of the translation that
produces it. A first slice is built and tested against the JVM; the rest is designed here and marked as such.
The section [What is built](#what-is-built) is the exact list, [The review](#the-review) what an independent
review found wrong in the first version and what was done about it, and [Open decisions](#open-decisions) what
the review says should be settled in the representation before more is built on it.

- The representation: a method is a **tree of effects**. What the code only computes is a term of the prover;
  what it does (a field read or written, an object made, a call) is a node of the tree, typed by what it gives.
- The translation: FrFlow reads the class's TASTy and does the symbolic evaluation **in Scala**, once, when the
  tree is emitted: a local variable becomes the value it has, a loop's state becomes the variables it assigns.
  The prover receives the result and evaluates nothing to find out what the code is.

It does not replace anything yet. The Ox model is proven over the trees of `FrFlow/Scala` and the executions of
`FrFlow/Executions.v` ([EXECUTIONS.md](EXECUTIONS.md)), and `lifted[Class]` structures over terms
([LIFTED.md](LIFTED.md)). Moving them onto this representation is the later stages below.

## What it has to serve

One representation, used four ways:

1. **Algebra and assumed laws.** Proofs about algebraic structures and about code written against a library
   known by its laws (cats-effect), with assumptions on how its operations evaluate and relate.
2. **JVM semantics.** The same code under a machine: threads, a heap, the memory model.
3. **Induction.** Proofs by induction on data and on a loop's turns.
4. **Separation logic.** Iris, with a rule per effect.

And two requirements from the work on Ox:

- **Symbolic evaluation at the Scala level.** Today Rocq recomputes what a method does from its tree at every
  proof step (`denote`), which is where the Ox proofs spend their time.
- **No strings for names.** Today a field, a method and a label are strings: a misspelt one is a valid term,
  what a field read gives has no type, and comparing two is comparing lists of characters.

## Prior work, and what is taken from it

- **Charon** (Rust) separates a front end that cleans the compiler's tree (structured control flow, resolved
  traits) from the tools that give it meaning. Taken: the emitter is its own stage with its own data type
  (`core.effect.Program`), separate from printing and from any meaning.
- **Aeneas** (Rust) evaluates symbolically outside the prover and emits pure functions in a result monad;
  loops become a body that says "again with this state" or "leave with this result". Taken: evaluation at
  emission, and that loop form. Not taken: memory disappearing altogether. That rests on Rust's ownership;
  Scala has aliasing and threads, so the heap stays, as effects.
- **DOT** is a calculus for Scala's types, in let-normal form; it has no classes, mutation, exceptions or
  threads. gDOT gives its types a meaning as Iris predicates over an untyped language. Taken: let-normal
  form (every effect's result is named once), and that Scala's types are not embedded in the prover's.
- **Program Logics à la Carte** builds Iris program logics over interaction trees, one signature of effects at
  a time. Taken: the tree is parametric in its effects, so a logic, a machine and a library's laws are each an
  interpretation of the same tree.

## The representation

The Rocq library is `modules/proof/rocq/FrFlow/Effect`. It depends on nothing else in FrFlow.

### Trees (`Tree.v`)

```coq
Inductive tree (E : Type -> Type) (A : Type) : Type :=
  | Ret (a : A)
  | Vis (X : Type) (e : E X) (k : X -> tree A)
  | Iter (St B : Type) (body : St -> tree (St + B)) (s : St) (k : B -> tree A).
```

- `Ret a` gives a value.
- `Vis e k` does one effect `e`, which gives an `X`, and goes on with `k`. The continuation is a function of the
  prover, so everything the code computes between two effects is ordinary Rocq: arithmetic, a test, a `match`.
- `Iter body s k` loops over a state: each turn gives the next state or what the loop gives.
- `E` is a parameter. A tree says which effects are done and in what order, and nothing of what they do.

The tree is inductive: a loop is a node, not an infinite unfolding, so the trees themselves admit induction and
structural recursion. `bind` is sequencing; `bind_ret` and `bind_bind` are proven (they take function
extensionality as a hypothesis, which the library already allows as an axiom).

### Code that may throw

```coq
Definition prog (A : Type) : Type := tree E (exn + A).
```

`ret`, `throw`, `then_` (sequencing that stops at a throw), `try_catch`, `try_finally`, `loop`, `again` and
`leave` are functions on trees. `try`/`catch`/`finally` therefore need no node of their own, and a throw that
leaves a loop is a loop that ends. The notations are `x <- p ;; k`, `'(x, y) <- p ;; k` and `p ;;; k`.

### Names and typed effects (`Sig.v`)

Each program comes with four finite types of its own, generated with it: its classes, fields, methods, and what
it calls of code that is not read (`outside`). A field's type and a method's inputs and result are functions of
the name. The effects are typed by them:

```coq
Inductive eff : Type -> Type :=
  | Get (o : ref) (f : field) : eff (field_ty f)
  | Put (o : ref) (f : field) (v : field_ty f) : eff unit
  | New (c : class) : eff ref
  | Call (o : ref) (m : method) (given : method_in m) : eff (exn + method_out m)
  | Ext (m : outside) (given : outside_in m) : eff (exn + outside_out m).
```

- A name that does not exist is not a term; two names are told apart by computation on constructors.
- Reading a field of numbers gives a `Z` with no step to recover the type, and writing a truth value into it
  does not type-check.
- `Call` is a method whose tree was read, called on an object. What it is called on is apart from what it is
  given, so that a call on no object is told from a call. `Ext` is anything else (the JDK, a library), about
  which the tree says nothing. The Scala name of an outside member is kept only as a label for people.
- The library is proven once over any such name types; a program instantiates it.

### Values

| Scala | In a tree | Note |
|---|---|---|
| `Int` | `Z`, operations `iadd`, `isub`, `imul`, `ineg` (`Int32.v`) | wrapped to 32 bits as the JVM does |
| `Boolean` | `bool` | |
| `Unit` | `unit` | |
| an object of any class | `ref`: `null` or `at_ n` | which class it is, the heap says |
| `a eq b`, `a ne b` (`Object`'s) | `same a b`, its negation | a method of the code named `eq` is a call |

- Any type of objects is a `ref`, also one that is not read (`String`, an array, a tuple): what is done with
  such a value is a call outside the code. A literal of one is refused.
- A `Z` in a tree is not confined to the range of `Int`. What the operations give is in range (`wrap`), but a
  method's inputs and what an outside call gives are any `Z`. A statement over all inputs is therefore about
  more inputs than the JVM has, which is sound; a statement that some input exists is not. See
  [Open decisions](#open-decisions).

A reference carries no class in its type: Scala's subtyping, variance and path-dependent types are not embedded
in Rocq's type system. They are resolved by the compiler before the tree is read and shape the tree without
being in it. Case classes and enums that are data are designed to be Rocq inductive types, as `RocqType`
derives them today (later stage).

### What a generated file looks like

`modules/project/src/test/resources/effects/Samples.v` is the emitter's output for the eight sample classes,
kept in the repository. Its parts, in order:

```coq
Inductive field : Type := | F_Account_opening | F_Account_balance | F_Account_refused | F_Bank_from | ...
Definition field_of (f : field) : class := match f with | F_Account_balance => C_Account | ... end.
Definition field_ty (f : field) : Type := match f with | F_Account_balance => Z | F_Bank_from => ref | ... end.
Definition method_in (m : method) : Type := match m with | M_Bank_transfer => Z | ... end.
Abbreviation prog := (Tree.prog eff exn).          (* the library at this program's names *)

Definition Bank_transfer (this : ref) (n : Z) : prog bool := ...   (* one definition per method *)

Definition body (m : method) : ref -> method_in m -> prog (method_out m) :=   (* what a Call runs *)
  match m with | M_Bank_transfer => fun this n => Bank_transfer this n | ... end.
```

Three methods and their trees, exactly as emitted:

```scala
def transfer(n: Int): Boolean =          // class Bank(from: Account, to: Account)
  val ok = from.withdraw(n)
  if ok then to.deposit(n)
  ok
```

```coq
Definition Bank_transfer (this : ref) (n : Z) : prog bool :=
  from <- get this F_Bank_from ;;
  ok <- call from M_Account_withdraw n ;;
  (if ok then
        to <- get this F_Bank_to ;;
        call to M_Account_deposit n ;;;
        ret tt
      else
        ret tt) ;;;
  ret ok.
```

```scala
def sumTo(n: Int): Int =
  var i = 0
  var s = 0
  while i < n do
    s = s + i
    i = i + 1
  s
```

```coq
Definition Counter_sumTo (this : ref) (n : Z) : prog Z :=
  '(i, s) <- loop (fun '(i, s) =>
      if i <? n then
        let s1 := iadd s i in
        let i1 := iadd i 1 in
        again (i1, s1)
      else
        leave (i, s)) (0, 0) ;;
  ret s.
```

```scala
def largest(a: Int, b: Int, c: Int): Int =
  var best = a
  if b > best then best = b
  if c > best then best = c
  best
```

```coq
Definition Numbers_largest (this : ref) (a : Z) (b : Z) (c : Z) : prog Z :=
  let test := b >? a in
  let best := if test then b else a in
  let test1 := c >? best in
  let best1 := if test1 then c else best in
  ret best1.
```

The second has no heap access although the Scala has two `var`s; the third has no effect at all.

## The translation flow

```text
Scala source
   │  scalac: types, overloads, givens and inlining resolved
   ▼
class file ───────────────────────────────► the JVM                    (what runs; what tests compare with)
TASTy (the class as typed, bodies included)
   │  the emitter, `frflow.dsl.compiled.effect`: symbolic evaluation, one pass per method;
   │  `NotRead` with file and line at anything it does not read
   ▼
`frflow.core.effect.Program`: name lists, typings, one `Tree` per method   (plain data; no prover in it)
   │  the printer, `frflow.proof.effect`
   ▼
one Rocq file over `FrFlow/Effect`
   ├──► `Run.v`: the tree run on a heap, one thread                     (built: the reference for tests)
   ├──► the pure view: a function, proven equal to the run              (designed)
   ├──► a machine with threads; executions                              (designed)
   ├──► Iris: a weakest precondition, a rule per effect                 (designed)
   └──► a library's signature and laws                                  (designed)
```

The stages are separate on purpose. The emitter knows Scala and no prover. `Program` knows neither. The
printer knows Rocq's syntax and nothing of Scala; a Lean printer would be a second one beside it.

### How the emitter evaluates

The emitter walks the typed tree in continuation-passing style. `expr(t, env)(next)` reads the expression `t`
and hands `next` two things: the expression's **value**, a pure term, and the **environment** as the expression
left it. `next` gives the rest of the tree. Effects are emitted in the order Scala evaluates, in front of what
follows; what is only computed stays inside the term.

The environment holds, for each variable in scope, the value it has now. That is the symbolic evaluation:

- A `val` or `var` of a method is not a place in memory. Reading it is its current value; assigning a `var`
  replaces that value in the environment. Every name in a tree is bound once (fresh names `i1`, `s1`), but
  for a loop's state, named in its turn and again after the loop.
- A choice whose two ways assign variables gives the variables' values together with its own.
- A loop's state is exactly the variables its test and body assign. Each turn takes their values and gives
  the next ones (`again`) or the ones the loop leaves with (`leave`).
- The name the code gives a value (`val ok = …`) is the name its binder gets in the tree.
- A statement's value is dropped: what it gave is not named, and a choice in that place gives no value.

### The rules that are implemented

Write `⟦e⟧ k` for the tree of `e` followed by `k`, where `k` receives `e`'s value.

| Scala | Tree |
|---|---|
| a literal, `this`, a local, a parameter | no node: the term itself is passed to `k` |
| `a + b`, `a < b`, `!a`, `a == b` on `Int`/`Boolean` | `⟦a⟧`, then `⟦b⟧`; the value is the term `iadd a b`, `a <? b`, … |
| `a && b`, `a \|\| b` with `b` only computing | the term `andb a b`, `orb a b` |
| `a && b`, `a \|\| b` where `b` has an effect | the choice it means: `if a then b else false`, `if a then true else b` |
| `val x = e; rest` | `⟦e⟧`, a `let x := …` if the value is not a name or a constant, then `rest` with `x` |
| `x = e` on a `var` of the method | `⟦e⟧`; the environment's value for `x` is replaced; no node |
| `o.f` on a field of the code read | `⟦o⟧`, then `v <- get o F ;;` |
| `o.c`, `c` a `final val` of a literal's type | `⟦o⟧`; the value is the literal, as Scala reads it, also before the field is written |
| `o.f = e` | `⟦o⟧`, `⟦e⟧`, then `put o F v ;;;` |
| `o.m(a, b)`, `m` a method of the code read | `⟦o⟧`, `⟦a⟧`, `⟦b⟧` in that order, then `r <- call o M (a, b) ;;` |
| `m(a, b)` on no written object, `m` of the code read | the same on `this` |
| `o.m(a, b)`, `m` anything else, `o` written | `⟦o⟧`, `⟦a⟧`, `⟦b⟧`, then `ext O (o, a, b)`; `O` is named when first met |
| `new C(a)` | `c <- new C_C ;;`, `⟦a⟧`, `call c M_C_new a ;;;`; the value is `c` |
| `a eq b`, `a ne b`, `Object`'s own | the term `same a b`, `negb (same a b)` |
| `if c then a else b`, both ways only computing | `let`s of `if c then … else …` terms, one per value that differs |
| `if c then a else b` otherwise | `'(v, x…) <- (if c then ⟦a⟧ else ⟦b⟧) ;;`, `x…` the variables either way assigns |
| `while c do b` | `'(x…) <- loop (fun '(x…) => ⟦c⟧ (if c then ⟦b⟧ again else leave)) (x… now) ;;` |
| a class's constructor | the method `new`: a `put` of each parameter that is a field, then the body in order |
| a method | `Definition C_m (this : ref) (inputs…) : prog T`, and a case of `body` |

Decisions the rules contain, and the scenario that covers each:

- **Order.** What a call is on is evaluated first, then its arguments left to right; operands left to right;
  what a field is written on before what is written (`ordering`, `edges`). The object is made before the
  constructor's arguments are evaluated, as the JVM does; no scenario can see that, since making an object has
  no other effect.
- **Fields before they are written** hold zero, `false` or `null` (`initial`), as on the JVM (`naming`: a
  field initialised from one declared after it).
- **A constant** (`final val c = 5`) is read as its literal, as Scala does, also before its field is written
  (`edges`).
- **A pure choice evaluates both ways as terms.** This is sound here because no operation read so far can
  fail. Division can; when it is read it must be an effect or a partial operation, not a term under `if`.
- **Names.** A method is `Class_method`, the second of a name `method_2` (`naming`). A local named as a Rocq
  keyword, a constructor or a name the file or the library defines gets a trailing `_` (`left_`). Two things
  that would be written alike (classes `A_b` with a field `c` and `A` with a field `b_c`), or a method written
  as a name the file defines, are refused (`Program.clashes`).

### What is refused

The rule is that Scala the emitter does not read is refused with its file and line (`NotRead`), never skipped
and never approximated. The first version broke this rule in eight places ([The review](#the-review)); each is
now a refusal or a correct reading, with a test. Refused:

- **Declarations:** traits, objects (so also a class with a companion in the files read), abstract or generic
  classes, classes with a parent, classes that are not `final` (a call of their method may run another's),
  nested classes and methods, type members, generic methods.
- **Members:** a `lazy val` or `inline` field, an `inline` method, a parameter passed by name or several as one
  (`Int*`).
- **Types:** `Long` and the other numbers, `Char`, functions; a literal of any type but `Int`, `Boolean`,
  `Unit` and `null`.
- **Expressions:** lambdas, `match`, `throw` and `try`, `return`, casts, `synchronized`, `/` and the bit
  operations, `==` on objects, a call of an `inline` method, a call outside the code on no object that is
  written (`require(…)`, a member of an `object`), a call of a setter by its name, a choice between values of
  two types whose value is used.

`EmitRefusalsSuite` checks ten of these. A secondary constructor is read (a method of the class).

### The rules that are designed, not implemented

| Scala | Tree | Needs |
|---|---|---|
| `throw e` | `throw v` | exception values as objects; `exn := ref` is already in the generated file |
| an access or call on `null` | `throw` of a `NullPointerException`, tested before the access | the same; today such a run is `Stuck` |
| `try b catch h finally f` | `try_finally (try_catch ⟦b⟧ ⟦h⟧) ⟦f⟧` | the library functions exist |
| `return e` in nested code | a leave of the method's tree, as a throw of a private kind | |
| `e match` on case classes, enums, literals | a Rocq `match`; no case is `throw MatchError` | data as inductive types |
| a virtual call on code read | `call` with the tree chosen by the receiver's class | `class_of` in the heap; a dispatch table |
| a lambda, a by-name argument | an object of a generated class holding what it captures, with `apply` in the method table | dispatch; see below |
| a `var` a closure captures | a cell: `new`, `get`, `put` | escape analysis in the emitter |
| `lazy val`, a Scala `object` | an effect "initialise once", then the initialiser's tree | as `Enter` in executions today |
| a method with no effect | also a plain Rocq function, `prog` only at its call sites | purity recorded per method |
| `Long`, `String`, arrays | their own value types and operations | decided one by one, each tested |

A closure cannot be "a Rocq function to a tree" kept as a value, which an earlier version of this page said. A
tree over `E` quantifies over the types of `E`'s results, so it lives one universe above them: no effect of `E`
can give a tree over `E`, and no field can hold one (checked in Rocq; universe polymorphism does not change
it). Closures are therefore first-order, as on the JVM: an object and a method.

## One representation, four uses

All four are interpretations of the same generated definitions. Only the reference run of the second is built.
Each has an obstacle the first version of this page did not state; they are stated here.

### Induction and pure views

- Code with no effect and no call is already a term: `Numbers_largest` above is `ret` of a Rocq expression,
  and proofs about it are proofs about that expression.
- A method that calls another, however pure, is a tree with `call` nodes. A proof about it unfolds `body`, or
  uses what is proven of the callee. The second needs a table of specifications per method, which is not
  built ([Open decisions](#open-decisions)).
- A loop is `loop body start`. The rule for it takes an invariant over the state, which is a tuple of the
  variables the Scala assigns, with their Scala names. The rule is not built; `Run.v` has the lemmas it would
  rest on (`run_step`, `run_more`).
- **Pure view** (designed): for a class that passes capture and separation checking, so that its fields are not
  aliased, each method gets a function `state -> inputs -> result * state` and a lemma that running the tree
  on a heap holding that state gives the function's result. This is what `lifted[Class]` produces today by a
  separate compiler; here it would be derived from the tree and proven, so both views are of one definition.
  A function of Rocq must end; a loop that Rocq cannot see end (`gcd` by subtraction) has a relation, not a
  function.

### The JVM

- **Built:** `Run.v` runs a tree on a typed heap, one thread, with fuel. `Get`/`Put` read and write a field of
  an object of the field's class, `New` appends an object whose fields hold `initial`, `Call` runs `body m` on
  an object of the method's class, `Ext` asks a parameter. A run ends one of three ways: `Gave` a value or a
  throw; `Stuck`, at an access or call on no object (where the JVM throws `NullPointerException`, which the
  trees do not have yet) or on an object of another class (which typed code does not do); `Spent`, out of
  fuel. A run that did not run out ends the same way with any more fuel (`run_more`, proven). It is the
  reference the emitter is tested against, not a model of threads.
- **Designed:** the frame machine of `FrFlow/Jvm/Machine.v` over these trees. A `Get`, `Put`, `New` or `Ext`
  is one step of one thread and one event of an execution. A `Call` is not one step: it pushes a frame, and
  its result is the callee's whole run, so the machine keeps a stack of continuations. A turn of a loop with
  no effect is a step with no event. With that, an invocation's events are a path through its method's tree,
  which the proof rules `step`/`pass` already walk. `Thread.start`, monitors and `AtomicBoolean` are `Ext`
  names given their meaning by the machine and assumed of it as today (`examples/ox/JDK.md`). What changes
  for the Ox proofs: the tree is a definition to unfold, not a value Rocq computes from syntax at each step,
  and a label is a constructor, not a string.
- **Missing for it:** whether a field is `volatile` or `final` is not recorded in `Program`, and the memory
  model needs it. `Ext` in `Run.v` cannot call back into the code read (a `Runnable`'s `run`).

### Libraries known by their laws (designed)

Three levels, chosen per library:

1. **Opaque.** An outside member is an `Ext` name with a typed input and result. What is assumed of it is a
   statement about what it gives, as with the JDK today.
2. **Pure by declaration.** A library signature may declare a member pure (a monoid's `combine`). It is then a
   function parameter of the generated file, not an effect, and its laws are hypotheses over that parameter.
   Proofs are algebra on terms and hold for every instance that meets the laws.
3. **A signature of effects.** For cats-effect, a method that gives an `IO[A]` is read as a tree over a
   signature `CatsE` (`RefModify`, `Start`, `Join`, …): `flatMap` is `then_`, `IO.pure` is `ret`, so the monad
   laws are `ret_then`, `then_ret` and `then_then`, proven in `Tree.v`, not assumed. What cats-effect promises
   beyond them ("`Ref.modify` is atomic") is assumed of any handler of `CatsE`. A handler into JVM effects (a
   `Ref` as an `AtomicReference`) can later replace those assumptions with proofs.

Obstacles:

- An `IO[A]` is a tree only where it is written. It cannot be the result of an effect or held in a field (the
  universe limit above), so an `IO` passed around as data needs a first-order form, as closures do.
- The typing tables go from a name to a `Type`, with no place for a type argument. Code over a type class
  (`combineAll[A: Monoid]`) has no type in `Sig` until generics either erase to `ref` or index the tables.
- `tree` is parametric in `E`, but the sum of two signatures, its injections and the interpretation of one
  signature into another are not built.

### Iris (designed)

A weakest precondition with one rule per effect: `Get o f` needs `o.f ↦ v` and gives `v`, typed by
`field_ty f`; `Put` updates it; `New` gives the new object's fields; `Iter` is by an invariant. Adequacy is
stated against the machine. Because points-to facts are typed by the field, a proof does not carry "this
value is a number" side conditions. The existing Iris language (`FrFlow/Bridge`) is over the old trees and
would be re-stated.

Obstacles:

- It is a recursion on the tree for `Vis` and `Iter`, not for `Call`: `body m` is no part of the caller's
  tree. Calls need the table of specifications, or Iris's step-indexing with a later at each call.
- A typed `catch`, `isInstanceOf` and dispatch need the class of a reference, which is only in the heap; a
  handler `exn -> prog A` cannot see it ([Open decisions](#open-decisions)).

## How it corresponds to Scala

| | |
|---|---|
| **Exact in what is built** | evaluation order; field reads and writes and calls on an object; object creation and constructor order; `Int` arithmetic with wrapping; `eq`; loops; short-circuit `&&`/`\|\|` |
| **No run where the JVM throws** | a field read or written, or a method called, on `null`: `Stuck`, no result |
| **By a rewriting the emitter does, so tested** | locals as values (no heap cell); loop state; choices returning assigned variables |
| **By a rewriting, not built** | pattern matching, dynamic dispatch, closures, initialise-once, exceptions |
| **Not represented** | Scala's types beyond the erased shape of values. They constrain which trees can be emitted; they are not in the trees |
| **Not modelled** | exceptions the JVM raises itself, class initialisation, allocation failure, stack depth, time. A tree's run takes fuel; a run that would overflow the JVM's stack is a run here |
| **Wider than the JVM** | a `Z` input or outside result outside the range of `Int` |

## What is trusted, and how it is tested

In this stage the emitter and the printer are trusted, and tested as follows.

- **Against the JVM** (`EffectRunSuite`, tagged Rocq). Nine scenarios over the sample classes are run on the
  JVM by reflection. For each, a Rocq lemma states that the run of the scenario's emitted tree gives the same
  number and is proven by `vm_compute`. The scenarios cover: fields read and written, two objects of one
  class, one object reached by two references, calls across objects, a loop over two variables, a loop inside
  a loop, a loop whose test has an effect, `&&` over a call, choices that assign variables, wrapping
  (`7^20 + (-3)^31` as `Int`), evaluation order as the digits of a number, a field read before it is written,
  a constant read before its field is written, a variable assigned in what a field is written on (in a choice
  and in a loop), a public `var` written from another class, methods named `eq` and `ne`, two methods of one
  name. Two more lemmas state that a call on `null`, and on an object of another class, is `Stuck`.
- **Kept output.** The generated file is in the repository and compared on every run, so any change to what
  is emitted appears in review as a diff of Rocq.
- **Refusals** (`EmitRefusalsSuite`, ten), and the printer on a hand-built program (`EffectPrintSuite`).

Limits of this testing, stated plainly:

- It is testing, not proof. It covers the constructs above on the inputs the scenarios use. The first version
  passed its six scenarios and was wrong in eight other places.
- TASTy is read as the compiler typed it, before inlining and erasure: the tree is of the code as written,
  and the emitter refuses what those later phases change (`inline`, by-name, `lazy`).
- It compares final results of single-threaded runs. It does not compare heaps, and there are no schedules
  because there are no threads yet.
- Nothing ties these trees to `FrFlow/Scala`'s `denote`. An earlier description of this design said Rocq would
  check `emitted = denote tree` once per method. That does not hold as stated: `denote` is over strings and one
  untyped value type, the emitted tree over generated names and typed values, so the two are not the same
  term. A link needs an erasure of names and values and a simulation proof, which is not built.

How trust is reduced later, in order of cost:

1. Each construct added arrives with a sample class and a scenario, and with programs that differ only in
   evaluation order.
2. Generated programs: random code in the supported fragment, compiled and compared the same way.
3. The emitter's rules written a second time in Rocq as a function on the reader's trees, proven to agree
   with `denote` under the erasure, and its output compared with the Scala emitter's per method. The Scala
   emitter is then checked, not trusted. Whether this is cheap enough on Ox's largest methods is not measured.

## What is built

| Part | Where | State |
|---|---|---|
| Trees, exceptions, loops, notations | `modules/proof/rocq/FrFlow/Effect/Tree.v` | built |
| Laws of sequencing | `Tree.v`: `bind_ret`, `bind_bind`, `ret_then`, `then_ret`, `then_then` | proven, over function extensionality |
| `Int` as the JVM computes it | `…/Effect/Int32.v` | `+`, `-`, `*`, unary `-`, comparisons |
| Names and typed effects | `…/Effect/Sig.v` | built |
| Typed heap, reference run | `…/Effect/Run.v` | one thread; `Gave`/`Stuck`/`Spent`; `run_more` proven |
| Program data | `frflow.core.effect` | built |
| Emitter | `frflow.dsl.compiled.effect` (`EmitEffects(cls, keep)`) | the rules listed as implemented |
| Printer | `frflow.proof.effect` (`PrintProgram`) | Rocq |
| Tests | `frflow.project.effects`, `frflow.proof.prover.EffectPrintSuite` | nine scenarios, ten refusals |

Not built: exceptions in the emitter, traits and dispatch, closures, data types, `match`, the pure view, the
machine and executions over these trees, library signatures, Iris, the link to `denote`, a model's use of any
of it (`lifted`, `Code_runs`). The emitter is called only by its tests.

## The review

An independent review of the first version (commit `a1f80f0`) rated it 2 of 10 for completeness against the
purpose above (6 of 10 as a first slice) and 5 of 10 for formal correctness. It emitted its own Scala and ran
both sides. It found the Rocq definitions right as far as they go (the laws of `bind` and `then_`,
`try_finally` in all throw cases, `Int32` at `Int.MinValue`), the core of the translation equal to the JVM on
31 comparisons, and these defects:

| Finding | Was | Now |
|---|---|---|
| A call on `null` gave the method's result | wrong | `Stuck`: `Call` carries its object, `Run.v` checks it; lemma in the run file |
| A by-name parameter read as a value | wrong | refused |
| An `inline` parameter read as a value | wrong | `inline` methods and calls of them refused |
| A `lazy val` field evaluated in the constructor | wrong | refused |
| A variable assigned in what a field is written on was not seen | wrong | seen; scenario `edges` |
| A method named `eq` or `ne` read as identity | wrong | only `Object`'s is; scenario `edges` |
| The setter of a public `var` emitted as doing nothing | wrong | not emitted; a call of it by name refused |
| A constant read before its field is written gave zero | wrong | the literal; scenario `edges` |
| Rocq that does not compile: branches of two types, locals `andb`/`orb`, names written alike | no refusal | refused, or renamed |
| `require(…)` given `this` as what it is called on | wrong shape | refused |
| A class another may extend, its calls bound to itself | unsound if extended | refused |
| `(if c then 1 else 0) + x` refused as "a value of type 1 \| 0" | too narrow | read |
| `Run.v`: one `None` for three ends; any object held any field | loose | three ends; class checked; `run_more` |
| A tree as a value in a tree (closures, `IO` values) | not realisable | design corrected above |

Not done, and listed next: the range of `Z`, the class in the reference, specifications for calls, field
flags, generics.

## Open decisions

The review recommends settling these in the representation before more is built on it. None is decided.

1. **The class of an object in its reference** (`at_ c n`) instead of only in the heap. Dispatch, a typed
   `catch` and `isInstanceOf` then compute on the reference; a points-to fact can be typed by class. Cost:
   references to objects of classes not read need a constructor of their own.
2. **A table of specifications per method**, so that a proof about a caller (by induction, or in Iris) uses
   what is proven of the callee and not `body`. Without it neither is a recursion on the tree.
3. **The range of `Int`.** Either a type of `Z` in range, or a generated hypothesis per `Z` input and per
   outside result. Until then only statements over all inputs are sound.
4. **Implicit exceptions.** Whether `Get`, `Put` and `Call` give `exn + …`, or the emitter writes a test for
   `null` before each. The second keeps the effects simple and is what the table of designed rules assumes.
5. **A relation beside the fuel.** A big-step `runs t h r` with `runs t h r <-> exists fuel, run fuel t h =
   Gave r` gives proofs a statement with no fuel in it; `run_more` is the lemma it needs.
6. **Generics**: erased to `ref`, or type arguments indexing the typing tables.
7. **Field flags** (`volatile`, `final`, `val`) in `Program`, for the machine.

## Stages

1. **Sequential Scala in full**: exceptions, `match` and data, traits and dispatch, closures, `String` and
   `Long`. Each with scenarios. Measure: the share of Ox's four files and of the examples' classes read.
2. **Pure view** for separation-checked classes, and `lifted[Class]` moved onto it. One compiler remains.
3. **Machine and executions** over these trees; Ox's generated code and proof rules moved; proof time compared
   with today's 30 CPU-minutes of hand proofs.
4. **Library signatures**: the JDK's as `Ext` names with today's assumptions; cats-effect as a signature.
5. **Iris** over the machine of stage 3.
6. **The checked emitter** (item 3 of the previous section).
