# Scala in the prover: one execution, values, and vocabularies

## 1. Introduction

FrFlow proves statements about real Scala. For that, the prover needs the code in a form that is faithful to
how Scala runs, small enough to reason about, and the same for every kind of proof: algebra over a library's
laws, induction, threads on the JVM, separation logic.

This page describes that form and the translation that produces it. In one sentence: **a program is a
sequence of operations over values, and the only thing that gives an operation meaning is what is stated
about it.**

How to read it:

- **Section 2** is the whole theory on one page.
- **Section 3** takes each idea of section 2 in turn, in the same order.
- **Section 4** is what exists in the repository and how it differs from the theory.
- **Section 5** is coverage: which Scala is read, which parts of the theory are built, what is open.

Status in brief: a first slice of the translation is built and tested against the JVM (plain classes, fields,
loops, calls). The theory is ahead of it. Each chapter ends with a **Status** line saying which of three it
is: *built* (in the library, tested), *proven on an example* (in
`modules/project/src/test/resources/effects/Worked.v`, compiled by a test), or *designed* (written here only).

## 2. The theory on one page

Five ideas.

1. **One execution.** There is one notion of running: Scala's own, one step after another. A method is a
   *program*: a tree that says which operations happen and in what order. What the code only computes
   (arithmetic, a test) is not a step; it is an ordinary term of the prover between the steps.
2. **Everything else is a value.** A number, an object reference, a lambda, an `IO` built with cats-effect:
   each is a value, and a value does nothing by existing. Building an `IO` is not running it; a lambda is code
   that has not run.
3. **Vocabularies.** Operations come in small groups: memory (read and write a field), calls, a monitor, cats'
   `Ref`, an outside system. A program is over exactly the vocabularies it uses, and its type says which. Code
   that mutates nothing has no memory operation; code that starts nothing has no thread operation.
4. **Meaning comes from statements.** A program says nothing about what an operation does. That is given by
   *laws* (assumed, or proven one layer down), by *definitions* (the operation's meaning as a program over
   lower vocabularies), and it is used by *claims*. These are FrFlow's assumptions, definitions and claims.
5. **Parallelism is interleaving of operations.** A method's program never changes. Running several at once
   means their operations interleave; other code can only get in between two operations. Whether a law may
   still be used then depends on a condition the law states.

One example through all five:

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
- **Vocabulary:** memory only (`mem`). Nothing about threads, cats or the JVM is in the definition.
- **Meaning:** stated separately: a read gives what is there, a write leaves what was written.
- **Parallelism:** the same `bump`, unchanged, supports three proven claims:
  - alone, it adds one;
  - two at once can lose an update (both read, then both write);
  - two at once, each holding a monitor, always count both.

What follows from the five ideas:

- **Minimal.** A proof sees only the vocabularies its program mentions, with their laws. A proof about cats code
  that touches no field never mentions an object.
- **Layered, per operation.** A proof goes down a layer (from cats laws to memory, from memory to the JVM) only
  at the operations where the code itself does.
- **One definition for every proof.** The generated program is the same whether it is reasoned about alone,
  interleaved, by rewriting with laws, or in a program logic.

## 3. The theory in detail

### 3.1 Programs

```coq
Inductive tree (E : Type -> Type) (A : Type) : Type :=
  | Ret (a : A)                                                    (* gives a value *)
  | Vis (X : Type) (e : E X) (k : X -> tree A)                     (* one operation, then the rest *)
  | Iter (St B : Type) (body : St -> tree (St + B)) (s : St) (k : B -> tree A).   (* a loop over a state *)
```

- `E` is the vocabulary: `E X` is an operation that gives an `X`. The tree is parametric in it.
- The continuation `k` is a function of the prover. Everything the code computes between two operations is
  inside it, as ordinary terms.
- A loop is one node: each turn gives the next state or the loop's result. The tree is inductive, so programs
  admit structural recursion and induction.
- Sequencing is `bind`. Its laws are proven: `bind_ret`, `bind_bind`.
- **Exceptions.** Code that may throw gives an exception or a value: `prog E exn A := tree E (exn + A)`.
  `throw`, sequencing that stops at a throw (`then_`), `try_catch`, `try_finally` and `loop` are functions on
  trees, with the laws `ret_then`, `then_ret`, `then_then` proven.

Notation used below: `x <~ e ;; rest` is `Vis e (fun x => rest)`.

**Status:** built (`FrFlow/Effect/Tree.v`).

### 3.2 Values

| Scala | Value in the prover |
|---|---|
| `Int` | a 32-bit number: operations wrap as the JVM's do |
| `Boolean`, `Unit` | `bool`, `unit` |
| case classes, enums | inductive types of the prover |
| an object | a *reference*: a type with an equality test and nothing else |
| a lambda, a by-name argument | a *function value*, made from what it captures (3.7) |
| a library's value, such as `IO[A]` | a type of the library's vocabulary, with the functions that build it (3.8) |

- A reference is abstract. Where an object is stored is not part of the theory; it appears only inside a
  model (3.6).
- A class, a field and a method are named by generated finite types, one constructor each. A name that does
  not exist is not a term, and what a field holds is a function of its name, so reading a field of numbers
  gives a number.
- Scala's types beyond this (subtyping, variance, path-dependent types, givens) are resolved by the compiler
  before the code is read. They decide which program is emitted and are not in it.

**Status:** numbers, truth values, references and generated names are built, with one difference: the
reference is still a concrete type (4.5). Data types, function values and library values are designed.

### 3.3 Vocabularies

A vocabulary is a family of operations, each typed by what it gives.

| Vocabulary | Operations |
|---|---|
| memory | read a field, write a field, make an object |
| calls | call a method of the code that was read |
| function values | apply one |
| monitor | enter, leave |
| cats `Ref` | `get`, `set`, `modify` with a pure function |
| cats `IO` | run a built value |
| fibers, threads | start a body, join |
| an outside system | one operation per member that is called |

- **Programs combine vocabularies.** A program over two is a tree over their sum; each node belongs to one:

  ```coq
  (* a cats Ref read, then a field read and written *)
  Definition counting_read : tree (sum1 ref mem) nat :=
    x <~ inl1 Read ;; seen <~ inr1 Get ;; _ <~ inr1 (Put (S seen)) ;; Ret x.
  ```
- **The minimality rule.** A program is over exactly the vocabularies its code uses. A proof about it has the
  laws of those vocabularies and no others.
- **An operation can say what its argument may do.** `start(body)` records the vocabulary of `body`. A law
  about fibers whose bodies touch no memory then cannot be applied to a body that does: it does not type-check.

**Status:** one fixed vocabulary is built (memory, calls and outside calls together). Sums and the minimality
rule are proven on an example (`counting_read`); the body vocabulary was type-checked outside the repository.

### 3.4 Statements

| FrFlow | Here |
|---|---|
| Declaration: a word known by what is said of it | an operation |
| Assumption | a law, taken as given |
| Claim | a law or a property of a program, proven |
| Definition | an operation's meaning as a program over lower vocabularies |

- **A law** says how operations relate or what one does. Three forms are used:
  - an equation between programs ("reading after `update f` is updating after reading, with `f` applied");
  - what an operation does to a state ("a monitor is entered only when nobody holds it");
  - a specification of a method (what it needs, what it guarantees).
- **A definition** gives an operation a meaning one layer down. A method call is defined by the method's
  program. A cats `Ref` can be defined as a field holding an `AtomicReference`.
- **A claim** is proven from the laws of the vocabularies its program mentions.
- **Laws are local.** A law quantifies over programs of its own vocabulary. It says nothing about a program
  that also has other operations, so mixing vocabularies never silently extends a law. To move an operation of
  one vocabulary past one of another, independence must be stated ("this `Ref` does not touch that field").

**Status:** designed. Three cats laws and one claim from them are proven on an example (3.9).

### 3.5 "Does the same"

Two different programs can do the same thing (`par a b` and "`a`, then `b`"), so the prover's own equality is
not the relation to use. There are two definitions and one theorem between them.

- **At a layer, with no model:** what the laws make equal, and nothing else. It is the smallest relation that
  is an equivalence, is kept by what comes before and after, and contains each law. This is an inductive
  definition with no semantics in it.
- **In a model:** no surrounding program can tell the two apart: placed before, after or *alongside* anything,
  they lead to the same results and final states. "Alongside" matters: `bump` and a single atomic increment
  have the same outcomes alone and different ones next to another thread.
- **The theorem:** a model satisfies a vocabulary when each law holds in the second sense; then everything
  derived in the first sense holds in that model. It is proven once per model.

Two practical points:

- A root claim is better stated about outcomes ("every run of this ends with …"). "Does the same" is the tool
  for rewriting inside proofs.
- With real choice between outcomes, the useful relation is one-directional: "does nothing that the other does
  not".

**Status:** the first definition is proven on an example (`same`, `adds_two`). The second and the theorem are
designed.

### 3.6 Models

A model gives every operation of a vocabulary something concrete to do and makes its laws true. It has three
uses, and a proof at a layer needs none of them:

- **Consistency:** laws that have a model do not contradict each other.
- **Testing:** an executable model runs a program, and its result is compared with the JVM's.
- **Discharging a layer:** a law assumed at one layer is proven in the model below it.

The executable model of memory is a list of objects. Three things live only there: a reference as a position
in that list; the bound on steps that an executable interpreter needs (*fuel*); and the outcome "stuck", for
an access that the laws say nothing about (a field of `null`). It is proven that a run that ended gives the
same result with any more fuel (`run_more`), so no statement needs to mention fuel.

**Status:** the executable model is built (`FrFlow/Effect/Run.v`). That it satisfies the laws of memory is
designed: those laws are not yet written down.

### 3.7 Function values and method calls

- **A lambda is a value.** It is made from what it captures. Applying it is an operation; the definition of
  that operation, for this lambda, is the lambda's body. Function values are first-order: a value holds what
  was captured, not a program. This is what the JVM does, and it avoids a real limit: in a prover, a program
  cannot be a value handled by programs of the same vocabulary (a universe constraint).
- **A method call is an operation** on a reference. Its definition is the method's program. Its specification
  is a law: a proof about a caller uses the callee's specification, and each method's program is proven to
  meet its own. Without specifications, a proof must unfold the callee, which never ends for recursion.
- **Purity is in the type.** Where a library requires a pure function (cats may run the function given to
  `Ref.modify` more than once), the operation takes a function of the prover. A lambda that does anything
  cannot be emitted as one, so the code is refused where it is written.

**Status:** calls and their definitions are built (the `body` table). Specifications and function values are
designed; `running_read` (3.8) is proven with a lambda in this form.

### 3.8 Values that are run later

With cats-effect or ZIO, Scala code builds a value and something else runs it. The theory has no second kind
of execution for this.

- **Building is a function on values.** `IO.pure(a)` and `io.flatMap(f)` return a value and do nothing.
- **Running is one operation,** and what it does is stated:
  - running `pure(a)` gives `a`;
  - running `io.flatMap(f)` runs `io`, applies `f` to what it gave, and runs the value that gave.
- **What happens when is then visible.** `IO.pure(next())` calls `next()` while building; `IO.delay(next())`
  puts the call in a function value. An `IO` that gives an `IO` is a value holding a value.

```scala
def read(io: IO[Int]): IO[Int] = io.flatMap { x => seen = seen + 1; IO.pure(x) }
```

`read` is a program that builds a value and does nothing else. From the two statements above and the lambda's
definition it is proven (`running_read`) that running that value runs `io`, then reads and writes `seen`, and
gives what `io` gave. The flat sequence is a consequence, obtained by rewriting; it is not assumed by the
translation.

**Status:** proven on an example. No library vocabulary is in the library.

### 3.9 Several programs at once

Programs running at once interleave at their operations.

- **The rule for the translation:** every operation on state that other code could touch is its own node.
  Operations are never merged at emission. A local variable becomes a value, which is safe because no other
  thread sees it, unless a lambda captures it.
- **Three cases,** read off the program:
  1. no operations: nothing can interleave; every sequential proof holds unchanged;
  2. operations on state nobody else touches: the sequential laws hold once that is shown;
  3. operations on shared state: the sequential laws do not apply.
- **Laws carry their condition.** The law of memory is "a read gives the last write". Alone, the last write is
  one's own, which is the sequential law. A monitor's law gives exclusivity, which restores it.

Threads of the JVM, proven by an invariant over all interleavings ("the number is what the two threads have
added so far"):

```coq
Lemma   bump_loses_one : ends jvm bump bump (0, None) tt tt (1, None).
Theorem guarded_counts_both x y s' : ends jvm guarded guarded (0, None) x y s' -> s' = (2, None).
```

cats-effect, proven by three rewrites with three laws, mentioning no thread and no object:

```coq
(* (ref.update(_ + 1), ref.update(_ + 1)).parTupled *> ref.get  gives what the Ref held plus two *)
Theorem both_then_read_adds_two :
  both_then_read ~~ bind read (fun x => bind (update (fun n => S (S n))) (fun _ => Ret (S (S x)))).
```

One layer down, the first of those laws is a theorem of the interleaving (`par_updates_holds`). Code that
reads and then sets is two operations; the law does not match it, and it provably loses an update
(`read_then_set_loses_one`).

**Status:** proven on an example, for two programs without loops. The general machine, and the theorem that
lifts a sequential claim to any execution under non-interference, are designed.

### 3.10 How proofs go

No proof about a program runs it or mentions fuel.

| Situation | Method |
|---|---|
| a sequence of operations | one step per node, by that operation's law |
| a loop | an invariant over its state (the variables the Scala assigns, by name) |
| a call | the callee's specification |
| library code | rewriting with the library's laws |
| programs at once | an invariant over all interleavings, or laws about running together |
| termination | a measure that decreases each turn |

**Status:** the Ox proofs use the first and fifth methods over the older trees (`step`, `pass`). For these
trees the methods exist only as used in `Worked.v`; general rules and their soundness are designed.

## 4. The implementation

### 4.1 Pipeline

```text
Scala source
   │  scalac
   ▼
class file ───────────────► the JVM                         (what runs; what tests compare with)
TASTy (the class as typed)
   │  emitter, `frflow.dsl.compiled.effect`: reads each method once; refuses what it does not read
   ▼
`frflow.core.effect.Program`: names, typings, one tree per method         (plain data)
   │  printer, `frflow.proof.effect`
   ▼
one Rocq file over `modules/proof/rocq/FrFlow/Effect`
```

The emitter knows Scala and no prover; the printer knows Rocq's syntax and no Scala. Nothing in FrFlow uses the
result yet except its tests: the Ox model and `lifted[Class]` are on the older representations.

### 4.2 The emitter

The emitter walks a method's typed tree with, for each variable in scope, the value it has now. This is the
symbolic evaluation, done once in Scala instead of at every proof step in the prover.

- A `val` or `var` of a method is the value it has; assigning a `var` replaces it. No memory is involved.
- A choice whose branches assign variables gives their values with its own.
- A loop's state is the variables its test and body assign.
- Operations are emitted in Scala's order of evaluation; what is only computed stays a term.
- Binders take the names the code gives (`val ok = …`).

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

`Counter.sumTo`, with two `var`s and a `while`, is emitted with no memory operation:

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

### 4.3 What is refused

Scala the emitter does not read is refused with its file and line, never skipped and never approximated.

- **Declarations:** traits, objects, abstract or generic classes, classes with a parent, classes that are not
  `final`, nested classes and methods, type members, generic methods.
- **Members:** a `lazy val` or `inline` field, an `inline` method, a parameter passed by name or repeated.
- **Types:** numbers other than `Int`, `Char`, functions; literals other than `Int`, `Boolean`, `Unit`, `null`.
- **Expressions:** lambdas, `match`, `throw`, `try`, `return`, casts, `synchronized`, `/`, bit operations,
  `==` on objects, a call of an `inline` method, a call outside the code on no written object, a call of a
  setter by name, a used choice between two types.
- **Names:** two things that would be written alike in the generated file.

### 4.4 The generated file

One file per program: the name types; the typing tables (what each field holds and belongs to, what each
method takes and gives); one definition per method; and the table `body` from a method's name to its program.
`modules/project/src/test/resources/effects/Samples.v` is the emitter's output for the test classes, kept in
the repository and compared on every run.

### 4.5 The prover library

| File | Contents |
|---|---|
| `Tree.v` | programs, sequencing and its laws, exceptions, loops |
| `Int32.v` | `Int` as a whole number with the JVM's wrapping |
| `Sig.v` | the vocabulary: `Get`, `Put`, `New`, `Call`, `Ext`, typed by the generated names |
| `Run.v` | the executable model: objects, a run that `Gave`, is `Stuck` or `Spent`, `run_more` |

How it differs from section 3:

- There is one vocabulary for every program, not one per use, and no sum.
- A reference is the concrete type `null | at_ n`, not an abstract one.
- No law is written down; the meaning of memory is only the executable model.
- Function values, data types, library vocabularies and specifications do not exist.

### 4.6 Tests, and what is trusted

- **Against the JVM** (`EffectRunSuite`). Nine scenarios run on the JVM and, as emitted programs, in the
  executable model; Rocq proves each result equal by computation. They cover fields, aliasing, calls, loops
  (nested, with an operation in the test), choices that assign, wrapping, evaluation order, a field and a
  constant read before they are written, a variable assigned inside a receiver, overloads, user methods named
  `eq`. Two lemmas show that a call on `null`, and on an object of another class, is stuck.
- **Kept output,** compared on every run, so a change in emission shows as a diff.
- **Refusals** (ten) and the printer on a hand-built program.
- **Worked examples** (`Worked.v`): every claim marked *proven on an example* in section 3, with no axiom.

What this does not give:

- The emitter and printer are tested, not proven. An independent review of the first version found eight kinds
  of accepted Scala whose program differed from the JVM while all tests passed. Each is now refused or read
  correctly, with a test.
- The tests compare final results of single-threaded runs.
- Nothing links these programs to the older trees and their meaning (`denote`).
- TASTy is the code as typed, before inlining and erasure; the emitter refuses what those phases change.

### 4.7 From the implementation to the theory

In order; each step is usable on its own.

1. Make the reference abstract; keep positions inside `Run.v`.
2. Split the vocabulary (memory, calls, outside) and add sums; the emitter computes each method's vocabulary.
3. Write the laws of memory; prove the executable model satisfies them.
4. Rules for steps and loops, method specifications, and their soundness.
5. Function values: lambdas and by-name arguments.
6. Data types, `match`, exceptions, dispatch.
7. Library vocabularies, cats-effect first: builders, running, laws.
8. The general interleaving of programs, the lifting theorem, and the Ox proofs moved onto it.
9. "Does the same" in a model, and the theorem of 3.5.

## 5. Coverage

### 5.1 Scala

| Construct | State | How |
|---|---|---|
| final classes, fields, constructors, methods | read | 4.2 |
| `Int`, `Boolean`, `Unit`, references | read | 3.2 |
| `if`, `while`, `&&`, `\|\|`, local `val` and `var` | read | 4.2 |
| calls of read code and of outside code | read | 4.2 |
| lambdas, by-name arguments | refused | function values (3.7) |
| case classes, enums, `match` | refused | data types of the prover |
| `throw`, `try`, `finally`, `return` | refused | the functions of 3.1 exist; emission does not |
| traits, inheritance, dynamic dispatch | refused | open (5.4) |
| generics | refused | open (5.4) |
| objects, `lazy val` | refused | an operation "initialise once" |
| `Long`, `String`, arrays, `/` | refused | each needs its value type and operations |
| `synchronized`, threads | refused | monitor and thread vocabularies (3.9) |
| cats-effect, ZIO | refused | library vocabularies (3.8) |

### 5.2 The theory

| Part | State |
|---|---|
| programs, sequencing, exceptions (3.1) | built |
| numbers, references, typed names (3.2) | built; reference not yet abstract |
| executable model, fuel confined to it (3.6) | built |
| calls defined by the method's program (3.7) | built |
| programs over several vocabularies (3.3) | proven on an example |
| "does the same" from laws (3.5) | proven on an example |
| a value run later, a lambda as a value (3.7, 3.8) | proven on an example |
| interleaving: threads with a monitor, cats laws, a law proven one layer down (3.9) | proven on an example |
| laws of memory; the model satisfies them (3.4, 3.6) | designed |
| specifications for calls; step and loop rules (3.7, 3.10) | designed |
| "does the same" in a model; its theorem (3.5) | designed |
| lifting a sequential claim to any execution (3.9) | designed |

### 5.3 The four uses

| Use | What the theory gives | State |
|---|---|---|
| algebra and assumed laws | library operations with laws; rewriting; no objects in the proof | on an example |
| JVM semantics | interleaving of the same programs under JVM-level laws | on an example; Ox not moved |
| induction | inductive trees, loop invariants, specifications | designed |
| separation logic | one rule per operation over the same programs | designed |

### 5.4 Open questions

- **Dispatch and typed `catch`.** Both need the class of an object. It can be an operation of its own
  vocabulary, or part of the reference. Not decided.
- **Exceptions the JVM raises itself** (`NullPointerException`). Either operations may fail, or the emitter
  writes the test before each access. The second keeps operations simple.
- **The range of `Int` in Rocq.** A method's inputs are any whole number there. Statements over all inputs are
  sound; statements that some input exists are not, until inputs are confined. A prover with a 32-bit type
  does not have the problem.
- **Generics.** Typing tables go from a name to a type, with no place for a type argument.
- **Fibers that start fibers.** The body's vocabulary would have to contain itself.
- **Field flags** (`volatile`, `final`) are not recorded; the JVM layer needs them.
- **Another prover.** The representation does not depend on Rocq. A Lean printer would be a second printer;
  the examples of 3.3 and 3.8 were type-checked in Lean by hand.

### Sources

- Charon and Aeneas (Rust): a front end separate from meaning; evaluation outside the prover; closures as
  plain values.
- Plotkin and Power, algebraic effects: a vocabulary with laws is a theory, and what satisfies it is a model.
- Interaction trees, and *Program Logics à la Carte*: programs as trees over a vocabulary, one logic per
  vocabulary.
- DOT and gDOT: Scala's types are not embedded in the prover's.
