# Scala in the prover: one execution, values, and vocabularies

## 1. Introduction

FrFlow proves statements about real Scala. For that, the prover needs the code in a form that is faithful to
how Scala runs, small enough to reason about, and the same for every kind of proof: algebra over a library's
laws, induction, threads on the JVM, separation logic.

This page describes that form and the translation that produces it. In one sentence: **a program is a
sequence of operations over values, and the only thing that gives an operation meaning is what is stated
about it.**

- **Section 2** is the whole theory on one page.
- **Section 3** details it: one or more chapters per idea of section 2, in the order of the ideas.
- **Section 4** is what exists in the repository.
- **Section 5** is coverage: which Scala is read, which parts of the theory are built, what comes next.

A first slice of the translation is built and tested against the JVM (plain classes, fields, loops, calls).
The theory is ahead of it. Each chapter of section 3 ends with its status, one of:

- **built**: in the library and tested;
- **on an example**: proven, with no axiom, for a small hand-written program in
  `modules/project/src/test/resources/effects/Worked.v`, which a test compiles;
- **designed**: written here only.

## 2. The theory on one page

Five ideas.

1. **One execution.** There is one notion of running: Scala's own, one step after another. A method is a
   *program*: it says which operations happen and in what order. What the code only computes (arithmetic, a
   test) is not a step; it is an ordinary term of the prover between the steps.
2. **Everything else is a value.** A number, an object reference, a lambda, an `IO` built with cats-effect:
   each is a value, and a value does nothing by existing. Building an `IO` is not running it; a lambda is code
   that has not run.
3. **Vocabularies.** Operations come in small groups, called vocabularies: memory, calls, a monitor, a
   library's operations. A program is over exactly the vocabularies its code uses, and its type says which.
4. **Meaning comes from statements.** A program says nothing about what an operation does. That is given by
   *laws* (assumed, or proven one layer down) and by *definitions* (an operation's meaning as a program over
   lower vocabularies); *claims* are proven from them. A *model* is something concrete that makes a
   vocabulary's laws true; it is needed to test and to check that laws are consistent, never to prove a claim.
5. **Parallelism is interleaving of operations.** A method's program never changes. Running several at once
   means their operations interleave: other code can only get in between two operations. Whether a law may
   still be used then depends on a condition the law states.

Proofs follow the program: one step per operation, by that operation's laws. No proof at a layer runs a
program.

**One example.** Code blocks are Rocq. `x <~ e ;; rest` means "do operation `e`, call what it gives `x`, go
on with `rest`"; `Ret v` gives the value `v`; `S x` is `x + 1`; `tt` is the unit value. The examples of
sections 2 and 3 are written by hand and simplified (memory is one number); section 4.2 shows emitted code.

```scala
final class Counter:
  private var count = 0
  def bump(): Unit = count = count + 1
```

```coq
Definition bump : tree mem unit := x <~ Get ;; _ <~ Put (S x) ;; Ret tt.
```

- **Execution:** two steps, a read and a write. The `+ 1` is a term, not a step.
- **Values:** the number read, `x`.
- **Vocabulary:** memory only (`mem`: `Get` and `Put`). Threads, monitors and the JVM are not in the definition.
- **Meaning:** stated separately: a read gives what is there, a write leaves what was written.
- **Parallelism:** this one definition supports three proven claims:
  - alone, it adds one;
  - two at once can lose an update (both read, then both write);
  - wrapped between entering and leaving a monitor, two at once always count both.

What follows from the five ideas:

- **Minimal.** A proof sees only the vocabularies its program mentions, with their laws. A proof about cats code
  that touches no field never mentions an object.
- **Layered, per operation.** A proof goes down a layer (from a library's laws to memory, from memory to the
  JVM) only at the operations where the code itself does.
- **One definition for every proof.** The generated program is the same whether it is reasoned about alone,
  interleaved, by rewriting with laws, or in a program logic.

## 3. The theory in detail

### 3.1 Programs (idea 1)

```coq
Inductive tree (E : Type -> Type) (A : Type) : Type :=
  | Ret (a : A)                                                    (* gives a value *)
  | Vis (X : Type) (e : E X) (k : X -> tree A)                     (* one operation, then the rest *)
  | Iter (St B : Type) (body : St -> tree (St + B)) (s : St) (k : B -> tree A).   (* a loop over a state *)
```

- `E` is the vocabulary: `E X` is an operation that gives an `X`.
- The rest of the program, `k`, is a function of the prover. Everything the code computes between two
  operations is inside it, as ordinary terms.
- A loop is one node. A turn of `body` gives the next state or the loop's result; the loop does a turn and
  then is the loop from the next state. The type is inductive, so programs admit induction.
- Sequencing two programs is `bind`. Its laws (`bind_ret`, `bind_bind`) are proven, from function
  extensionality.
- **Exceptions.** Code that may throw gives an exception or a value: `prog E exn A := tree E (exn + A)`.
  `throw`, sequencing that stops at a throw (`then_`), `try_catch`, `try_finally` and `loop` are functions on
  programs, with their laws proven (`ret_then`, `then_ret`, `then_then`).

**Status:** built (`FrFlow/Effect/Tree.v`).

### 3.2 Values (idea 2)

| Scala | Value in the prover |
|---|---|
| `Int` | a whole number whose operations wrap to 32 bits as the JVM's do |
| `Boolean`, `Unit` | `bool`, `unit` |
| case classes, enums | inductive types of the prover |
| an object | a *reference*: a type with an equality test and nothing else |
| a lambda, a by-name argument | a *function value* (3.3) |
| a library's value, such as `IO[A]` | a type of the library, with the functions that build it (3.4) |

- A reference is abstract. Where an object is stored is not part of the theory; it appears only in a model.
- Classes, fields and methods are named by generated types: one constructor per class, per field, per method.
  A name that does not exist is not a term, and what a field holds is a function of its name, so reading a
  field of numbers gives a number.
- Scala's types beyond this (subtyping, variance, path-dependent types, givens) are resolved by the compiler
  before the code is read. They decide which program is emitted and are not in it.

**Status:** numbers, truth values, references and names are built, with two differences: the reference is
still a concrete type, and a number given to a method is not confined to 32 bits (5.5). The rest is designed.

### 3.3 Function values and method calls (idea 2)

- **A lambda is a value,** made from what it captures. Applying it is an operation, and the definition of that
  operation, for this lambda, is the lambda's body. A function value holds what was captured, not a program.
  This is what the JVM does, and it respects a limit of the prover: a program cannot be what an operation
  gives back, nor what a field holds. (A program can be what an operation is *given*: a fiber's body.)
- **A method call is an operation** on a reference. Its definition is the method's program. Its specification
  (what it needs, what it guarantees) is a law: a proof about a caller uses the callee's specification, and
  each method's program is proven to meet its own. Without specifications a proof must unfold the callee,
  which does not end for recursion.
- **Purity is in the type.** Where a library requires a pure function (cats may run the function given to
  `Ref.modify` more than once), the operation takes a function of the prover. A lambda that does anything
  cannot be emitted as one, so such code is refused where it is written.

**Status:** calls and their definitions are built (the `body` table). A lambda as a value is on an example
(3.4). Specifications are designed.

### 3.4 Values that are run later (idea 2)

With cats-effect or ZIO, Scala code builds a value and something else runs it. There is no second kind of
execution for this.

- **Building is a function on values.** `IO.pure(a)` and `io.flatMap(f)` return a value and do nothing.
- **Running is one operation.** What it does is stated, here as two laws. `Run io` is the operation; `Apply f x`
  applies a function value; `t ~~ u` reads "`t` does the same as `u`" (3.8). Type arguments are left out:

  ```coq
  Run (io_pure a)        ~~  Ret a
  Run (io_flatMap io f)  ~~  x <~ Run io ;; next <~ Apply f x ;; Run next
  ```
- **What happens when is visible.** `IO.pure(next())` calls `next()` while the value is built;
  `IO.delay(next())` puts the call in a function value. An `IO` that gives an `IO` is a value holding a value.

```scala
def read(io: IO[Int]): IO[Int] = io.flatMap { x => seen = seen + 1; IO.pure(x) }
```

`read` builds a value and does nothing else. Its lambda is the function value `read_1 this`, with its body as
the definition of applying it:

```coq
Apply (read_1 this) x  ~~  seen <~ Load this ;; _ <~ Store this (S seen) ;; Ret (io_pure x)
```

From these three statements it is proven (`running_read`) that running the value `read` built runs `io`, then
reads and writes `seen`, and gives what `io` gave:

```coq
Run (io_flatMap io (read_1 this))  ~~  x <~ Run io ;; seen <~ Load this ;; _ <~ Store this (S seen) ;; Ret x
```

The flat sequence is a consequence obtained by rewriting. The translation does not assume it.

**Status:** on an example. No library is in the prover library yet.

### 3.5 Vocabularies (idea 3)

A vocabulary is a family of operations, each typed by what it gives.

| Vocabulary | Operations |
|---|---|
| memory | read a field, write a field, make an object |
| calls | call a method of the code that was read |
| function values | apply one |
| monitor | enter, leave |
| cats `Ref` | `get`, `set`, `modify` with a pure function |
| a library's values | run one |
| fibers, threads | start a body, join |
| an outside system | one operation per member that is called |

- **Programs combine vocabularies.** A program over two is over their sum: each node is an operation of the
  first (`inl1`) or of the second (`inr1`). In the example of section 2, `bump` is over memory, and the guarded
  version is `bump` itself, placed among the monitor's operations (`within` turns a program over memory into
  the same program over both):

  ```coq
  Definition guarded : tree (sum1 monitor mem) unit :=
    _ <~ inl1 Lock ;; bind (within bump) (fun _ => _ <~ inl1 Unlock ;; Ret tt).
  ```
- **The minimality rule.** A program is over exactly the vocabularies its code uses, and a proof about it has
  the laws of those and no others. The claim that `bump` alone adds one is stated and proven with memory
  only.
- **An operation can say what its argument may do.** Running two bodies together (`Par a b`) records the
  vocabulary of the bodies. A law about bodies that only use a `Ref` cannot be applied to a body that also
  writes a field: it does not type-check.

**Status:** one fixed vocabulary is built (memory, calls and outside calls together). Sums, separate
vocabularies and a body's vocabulary are on an example.

### 3.6 Statements (idea 4)

| FrFlow | Here |
|---|---|
| Declaration: a name with no definition, known only through statements | an operation |
| Assumption | a law, taken as given |
| Claim | a law, or a property of a program, proven |
| Definition | an operation's meaning as a program over lower vocabularies |

- **A law** says how operations relate or what one does. Three forms are used:
  - an equation between programs ("two updates in a row are one update");
  - what an operation does to a state ("a monitor is entered only when no thread holds it");
  - a specification of a method.
- **A definition** gives an operation a meaning one layer down. A method call is defined by the method's
  program; a cats `Ref` can be defined as a field holding an `AtomicReference`.
- **A claim** is proven from the laws of the vocabularies its program mentions.
- **Laws are local.** A law speaks of programs of its own vocabulary. It says nothing about a program that
  also has other operations, so mixing vocabularies never silently extends a law. To move an operation of one
  vocabulary past one of another, their independence must be stated ("this `Ref` does not touch that field").

**Status:** designed as a part of FrFlow. On an example: laws in the first two forms, and claims from them.

### 3.7 Models (idea 4)

A model gives every operation of a vocabulary something concrete to do and makes its laws true. It has three
uses, and a proof at a layer needs none of them:

- **Consistency:** laws that have a model do not contradict each other.
- **Testing:** an executable model runs a program, and the result is compared with the JVM's.
- **Discharging a layer:** a law assumed at one layer is proven in the model below it.

The executable model of memory is a list of objects. Three things exist only there:

- a reference as a position in that list;
- *fuel*, the bound on steps that an interpreter written in a prover must have. A run that ended gives the
  same result with any more fuel (`run_more`, proven), so no statement needs to mention it;
- the outcome "stuck", for an access the laws say nothing about (a field of `null`).

**Status:** the executable model is built (`FrFlow/Effect/Run.v`). That it satisfies the laws of memory is
designed: those laws are not yet written down.

### 3.8 "Does the same" (idea 4)

Two different programs can do the same thing (two computations run together, and the same two one after the
other), so the prover's own equality is not the relation to use. It is written `~~`, and has two definitions
and one theorem between them.

- **At a layer, with no model:** what the laws make equal, and nothing else. It is the smallest relation that
  is an equivalence, is preserved when the same program is put before or after both sides, and contains each
  law. This is an inductive definition with no semantics in it.
- **In a model:** no surrounding program can tell the two apart: placed before, after or *alongside* anything,
  they lead to the same results and final states.
- **The theorem:** a model satisfies a vocabulary when each law holds in the second sense; then everything
  derived in the first sense holds in that model. It is proven once per model.

Three practical points:

- **"Alongside" makes laws conditional.** Alone, `bump` and a single atomic increment have the same outcomes;
  next to another thread they do not. A law that holds only when nothing else touches the state must say so.
  The cats laws of 3.9 are stated for a `Ref` that only the program at hand uses.
- **Roots are better stated about outcomes** ("every run of this ends with …"). `~~` is the tool for rewriting
  inside proofs.
- **With a real choice between outcomes** the useful relation is one-directional. Two updates that do not
  commute, run together, happen in one of two orders: the pair does nothing that "one of the two orders" does
  not, and is equal to neither order.

**Status:** the first definition is on an example (`same`, `adds_two`). The second and the theorem are
designed.

### 3.9 Several programs at once (idea 5)

Programs running at once interleave at their operations.

- **The rule for the translation:** every operation on state that other code could touch is its own node.
  Operations are never merged at emission. A local variable becomes a value, which is safe because no other
  thread sees it, unless a lambda captures it.
- **Three cases,** read off the program:
  1. no operations: nothing can interleave, and every sequential proof holds unchanged;
  2. operations on state nobody else touches: the sequential laws hold once that is shown;
  3. operations on shared state: the sequential laws do not apply.
- **Laws carry their condition.** The law of memory is "a read gives the last write". Alone, the last write is
  one's own; at once, it may be another's. A monitor's law gives exclusivity, which restores the sequential
  reading.
- **The JVM.** Interleaving of reads and writes is the meaning of a field that is `volatile` or accessed
  without a data race. Of a plain field that threads race on, the JVM allows more (JLS 17.4). So the JVM layer
  either proves race freedom, as the Ox proofs do, or claims nothing of such a field. A lost update is among
  the outcomes the JVM allows.

**Threads of the JVM.** `ends law a b s x y s'` reads: `a` and `b`, run at once from the state `s` under the
laws `law`, can both end, giving `x` and `y` and leaving the state `s'`. `many alone c c'` is one thread going
from `c` to `c'` in some number of steps. Under `stores` (memory) the state is the number; under `jvm` (memory
and a monitor) it is the number and which thread holds the monitor.

```coq
Lemma   bump_alone_adds_one n : many alone (bump, n) (Ret tt, S n).
Lemma   bump_loses_one : ends (fun _ => stores) bump bump 0 tt tt 1.
Theorem guarded_counts_both x y s' : ends jvm guarded guarded (0, None) x y s' -> s' = (2, None).
```

The last is proven by an invariant over all interleavings: "the number is what the two threads have added so
far", stated over where each thread is in its program.

**cats-effect.** The program is `(ref.update(_ + 1), ref.update(_ + 1)).parTupled *> ref.get`. Three laws are
assumed, of a `Ref` nothing else touches: two updates run together are one after the other (in either order,
when the functions commute); two updates in a row are one; reading after an update is updating after reading.
The claim is proven by three rewrites and mentions no thread and no object:

```coq
(* it gives what the Ref held plus two, and leaves that in it *)
Theorem both_then_read_adds_two :
  both_then_read ~~ bind read (fun x => bind (update (fun n => S (S n))) (fun _ => Ret (S (S x)))).
```

**One layer down.** With an update as one operation, what the first law says of outcomes is a theorem of the
interleaving (`par_updates_holds`: the `Ref` ends as one of the two orders leaves it). Code that reads and
then sets is two operations; the law does not match it, and it provably loses an update
(`read_then_set_loses_one`).

**Status:** on an example, for two programs without loops. The interleaving of any number of programs, and
the theorem that lifts a sequential claim to any execution when nothing interferes, are designed.

### 3.10 How proofs go

No proof at a layer runs a program or mentions fuel. (The tests do: 4.5.)

| Situation | Method |
|---|---|
| a sequence of operations | one step per node, by that operation's law |
| a loop | an invariant over its state (the variables the Scala assigns, by name) |
| a call | the callee's specification |
| library code | rewriting with the library's laws |
| programs at once | an invariant over all interleavings, or laws about running together |
| termination | a measure that decreases each turn |
| ownership | a separation logic with one rule per operation |

**Status:** the proofs of the Ox model use the first and fifth methods, over an older representation
(`step`, `pass`). For these programs the methods exist only as used in `Worked.v`; general rules, their
soundness and the separation logic are designed.

## 4. The implementation

Words differ in the code: a vocabulary is `eff` (effects), an operation an effect, a program a `tree` or a
`prog`.

### 4.1 Pipeline

```text
Scala source
   │  scalac
   ▼
class file ───────────────► the JVM                         (what runs; what tests compare with)
TASTy (the class as typed)
   │  emitter, `frflow.dsl.compiled.effect`: reads each method once; refuses what it does not read
   ▼
`frflow.core.effect.Program`: names, typings, one program per method      (plain data)
   │  printer, `frflow.proof.effect`
   ▼
one Rocq file over `modules/proof/rocq/FrFlow/Effect`
```

The emitter knows Scala and no prover; the printer knows Rocq's syntax and no Scala. Nothing in FrFlow uses the
result yet except its tests: the Ox model and `lifted[Class]` structures are on older representations
([EXECUTIONS.md](EXECUTIONS.md), [LIFTED.md](LIFTED.md)).

### 4.2 The emitter

The emitter walks a method's typed tree holding, for each variable in scope, the value it has now. This is
symbolic evaluation, done once in Scala instead of at every proof step in the prover.

- A `val` or `var` of a method is the value it has; assigning a `var` replaces it. No memory is involved.
- A choice whose branches assign variables gives their values with its own.
- A loop's state is the variables its test and body assign.
- Operations are emitted in Scala's order of evaluation; what is only computed stays a term.
- Names in the output are the names the code gives (`val ok = …`).

| Scala | Emitted |
|---|---|
| literal, `this`, local, parameter | a term |
| `+ - *`, comparisons, `!`, `==` on `Int`/`Boolean` | a term (`iadd a b`, `a <? b`, …) |
| `a && b`, `a \|\| b` | a term; a choice when `b` does something |
| `val x = e`, `x = e` on a local | `e`, then the value under the name `x` |
| `o.f`, `o.f = e` | `get o F`, `put o F v` |
| `o.c`, `c` a `final val` of a literal's type | the literal, as Scala reads it |
| `o.m(a, b)`, `m(a, b)` of the code read | `o`, then `a`, `b`, then `call o M (a, b)` |
| `o.m(a, b)` of other code, `o` written | `ext O (o, a, b)` |
| `new C(a)` | `new C_C`, then `a`, then `call c M_C_new a` |
| `a eq b`, `a ne b` (`Object`'s) | a term |
| `if`, both branches only computing | terms |
| `if` otherwise | a branch, giving its value and the variables assigned |
| `while c do b` | `loop` over the assigned variables |
| a constructor | the method `new`: each parameter that is a field is written, then the body in order |

Scala the emitter does not read is refused with its file and line, never skipped and never approximated; 5.1
lists what.

`Counter.sumTo`, with two `var`s and a `while`, as emitted. `prog Z` is a program that gives a number or
throws; `x <- p ;; rest` sequences programs; `again` and `leave` end a turn of the loop; `iadd` is addition
with wrapping. There is no memory operation in it:

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

### 4.3 The generated file

One file per program: the name types; the typing tables (what each field holds and belongs to, what each
method takes and gives); one definition per method; and the table `body` from a method's name to its program.
`modules/project/src/test/resources/effects/Samples.v` is the emitter's output for the test classes, kept in
the repository and compared on every run.

### 4.4 The prover library

| File | Contents |
|---|---|
| `Tree.v` | programs, sequencing and its laws, exceptions, loops |
| `Int32.v` | `Int` as a whole number (`Z`) with the JVM's wrapping |
| `Sig.v` | the one vocabulary: `Get`, `Put`, `New`, `Call`, `Ext`, typed by the generated names; the reference `null \| at_ n` |
| `Run.v` | the executable model: objects, a run that `Gave`, is `Stuck` or `Spent`, `run_more` |

Section 5.2 says how this differs from the theory.

### 4.5 Tests, and what is trusted

- **Against the JVM** (`EffectRunSuite`). Nine scenarios run on the JVM and, as emitted programs, in the
  executable model, with fuel; Rocq proves each result equal by computation. They cover fields, aliasing,
  calls, loops (nested, with an operation in the test), choices that assign, wrapping, evaluation order, a
  field and a constant read before they are written, a variable assigned inside a receiver, overloads, user
  methods named `eq`. Two lemmas show that a call on `null`, and on an object of another class, is stuck.
- **Kept output,** compared on every run, so a change in emission shows as a diff.
- **Refusals** (ten cases) and the printer on a hand-built program.
- **Worked examples** (`Worked.v`): everything section 3 marks "on an example".

What this does not give:

- The emitter and printer are tested, not proven. An independent review of the first version found eight kinds
  of accepted Scala whose program differed from the JVM while all tests passed. Each is now refused or read
  correctly, with a test.
- The tests compare final results of single-threaded runs.
- Nothing links these programs to the older representation and its meaning.
- TASTy is the code as typed, before inlining and erasure; the emitter refuses what those phases change.
- The worked examples are hand-written programs over one number, not emitted code, and have no objects.

## 5. Coverage

### 5.1 Scala

Read:

- final classes with fields, constructors (also secondary ones) and methods;
- `Int`, `Boolean`, `Unit`; any object type as a reference, including types that are not read (`String`, an
  array), whose methods are then outside calls;
- `if`, `while`, `&&`, `||`, local `val` and `var`, field reads and writes, `new`;
- calls of the code read and of outside code.

Refused, with how it would be read:

| Construct | How |
|---|---|
| lambdas, by-name arguments | function values (3.3) |
| case classes, enums, `match` | data types of the prover |
| `throw`, `try`, `finally`, `return` | the functions of 3.1 exist; emission does not |
| objects, `lazy val` | an operation "initialise once" |
| `synchronized`, threads | monitor and thread vocabularies (3.9) |
| cats-effect, ZIO | library vocabularies (3.4) |
| other numbers, `Char`, `/`, bit operations, literals of other types | each needs its value type and operations |
| traits, inheritance, classes that are not `final`, dynamic dispatch | open (5.5) |
| generic classes and methods | open (5.5) |

Refused with no reading planned: `inline` methods and fields, repeated parameters, nested classes and
methods, type members, casts, `==` on objects, a call outside the code with no written receiver, a setter
called by name, a used choice between values of two types, two things that would get one name in the file.

### 5.2 The theory

| Part | State |
|---|---|
| programs, sequencing, exceptions (3.1) | built |
| numbers, references, typed names (3.2) | built; the reference is concrete, numbers are not confined |
| calls defined by the method's program (3.3) | built |
| executable model, fuel confined to it (3.7) | built |
| a lambda as a value; a value that is run later (3.3, 3.4) | on an example |
| separate vocabularies, sums, a body's vocabulary (3.5) | on an example; the library has one vocabulary |
| "does the same" from laws (3.8) | on an example |
| interleaving: one definition alone and at once, a monitor, cats laws, a law one layer down (3.9) | on an example, two programs, no loops |
| laws of memory, and that the model satisfies them (3.6, 3.7) | designed |
| specifications for calls; rules for steps and loops (3.3, 3.10) | designed |
| "does the same" in a model, and its theorem (3.8) | designed |
| lifting a sequential claim to any execution (3.9) | designed |
| separation logic (3.10) | designed |

### 5.3 The four uses

| Use | What the theory gives | State |
|---|---|---|
| algebra and assumed laws | library operations with laws; rewriting; no objects in the proof | on an example |
| JVM semantics | interleaving of the same programs under JVM-level laws | on an example; the Ox proofs are not moved |
| induction | inductive programs, loop invariants, specifications | designed |
| separation logic | one rule per operation over the same programs | designed |

### 5.4 Order of work

Each step is usable on its own.

1. Make the reference abstract; keep positions inside `Run.v`.
2. Split the vocabulary (memory, calls, outside) and add sums; the emitter computes each method's vocabulary.
3. Write the laws of memory; prove the executable model satisfies them.
4. Rules for steps and loops, method specifications, and their soundness.
5. Function values: lambdas and by-name arguments.
6. Data types, `match`, exceptions, dispatch.
7. Library vocabularies, cats-effect first: builders, running, laws.
8. The general interleaving of programs, the lifting theorem, and the Ox proofs moved onto it.
9. "Does the same" in a model, and the theorem of 3.8.

### 5.5 Open questions

- **Dispatch and typed `catch`.** Both need the class of an object. It can be an operation of its own
  vocabulary, or part of the reference. Not decided.
- **Exceptions the JVM raises itself** (`NullPointerException`). Either operations may fail, or the emitter
  writes the test before each access. The second keeps operations simple.
- **The range of `Int` in Rocq.** A method's inputs are any whole number there. Statements over all inputs are
  sound; statements that some input exists are not, until inputs are confined.
- **Generics.** Typing tables go from a name to a type, with no place for a type argument.
- **Re-entering a monitor.** The example's law does not allow it; the JVM's monitor does.
- **Field flags** (`volatile`, `final`) are not recorded; the JVM layer needs them.
- **Another prover.** The representation does not depend on Rocq; a Lean printer would be a second printer.

### Sources

- Charon and Aeneas (Rust): a front end separate from meaning; evaluation outside the prover; closures as
  plain values.
- Plotkin and Power, algebraic effects: a vocabulary with laws is a theory, and what satisfies it is a model.
- Interaction trees, and *Program Logics à la Carte*: programs as trees over a vocabulary, one logic per
  vocabulary.
- DOT and gDOT: Scala's types are not embedded in the prover's.
