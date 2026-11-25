# Representation of compiled Scala in the prover

## 1. Introduction

### 1.1 Purpose

FrFlow proves statements about Scala code. This document specifies the form in which that code is given to
the prover, and the translation from compiled Scala to that form. The form is required to follow Scala's
evaluation, and to be the same definition for each kind of proof FrFlow supports or plans to support: proofs
from a library's laws, proofs by induction, proofs about threads on the JVM, and proofs in a separation logic.

### 1.2 Structure

- Section 2 defines the terms and summarises the model.
- Section 3 specifies each part of the model.
- Section 4 specifies the translation pipeline and describes its implementation in the repository.
- Section 5 lists coverage: the Scala that is read, the parts of the model that are implemented, the order of
  remaining work, and open questions.

### 1.3 Status terms

Each subsection of section 3 ends with a status. The terms are:

| Term | Meaning |
|---|---|
| built | Present in the library and covered by tests. |
| on an example | Proven without axioms for a small hand-written program in `modules/project/src/test/resources/effects/Worked.v`. A test compiles that file. |
| designed | Specified in this document only. |

The implementation covers classes, fields, loops and calls, and is tested against the JVM. The rest of the
model is on an example or designed.

### 1.4 Notation

Code blocks are Rocq unless marked otherwise.

| Notation | Meaning |
|---|---|
| `x <~ e ;; rest` | Perform operation `e`, bind its result to `x`, continue with `rest`. |
| `Ret v` | Give the value `v`. |
| `S x`, `tt` | `x + 1`; the unit value. |
| `t ~~ u` | Programs `t` and `u` are equivalent (3.8). |

The programs in sections 2 and 3 are written by hand and simplified: memory is a single number. Section 4.4
shows emitted code.

## 2. Overview

### 2.1 Terms

| Term | Definition |
|---|---|
| operation | A single step of execution that is not pure computation: a field read, a field write, a call. An operation has a result type. |
| program | A tree that fixes which operations are performed and in what order. Each method is translated to one program. |
| value | Anything a program computes with: a number, a reference, a function value, a value built with a library. |
| vocabulary | A set of operations. A program is typed by the vocabularies whose operations it contains. |
| law | A statement about operations. A law is assumed, or proven in a lower layer. |
| definition | The meaning of an operation as a program over other vocabularies. |
| claim | A statement about a program, proven from laws and definitions. |
| model | A concrete interpretation of a vocabulary in which its laws hold. |
| layer | A set of vocabularies with their laws. A layer is lower than another if it defines the other's operations. |

Laws, definitions and claims correspond to FrFlow's assumptions, definitions and claims. An operation
corresponds to a declaration.

### 2.2 Summary

1. Execution. There is one notion of execution, Scala's sequential evaluation. A program lists the operations
   of a method in evaluation order. Pure computation between operations is not a step. It is represented as
   terms of the prover.
2. Values. Everything that is not an operation is a value. An `IO` built with cats-effect is a value, and
   building it performs no operation. A lambda is a value, and creating it performs no operation.
3. Vocabularies. A program contains only operations of the vocabularies its source code uses. The program's
   type records those vocabularies.
4. Statements. A program does not specify what its operations do. Laws and definitions specify it. Claims are
   proven from them. A model is used to test programs and to show that laws are consistent. A proof of a claim
   does not use a model.
5. Concurrent execution. A method has the same program whether it runs alone or concurrently. Concurrent
   execution interleaves the operations of several programs. Each law states the condition under which it
   holds in the presence of other programs.

A proof proceeds along the program, one operation at a time, using the laws of that operation. A proof at a
layer does not execute the program.

### 2.3 Translation

Translation has two stages and two intermediate representations (4.1).

1. Normalisation. Compiled Scala (TASTy) is rewritten to *normalised Scala*: a typed form in which evaluation
   order, pattern matching, closures and dispatch are explicit. No meaning is assigned.
2. Evaluation. Normalised Scala is evaluated symbolically to a *program representation*: one program per
   method, as defined in 2.1.

A printer writes the program representation in the syntax of a prover. The two stages correspond to Charon
and Aeneas in the Rust toolchain (References).

### 2.4 Example

```scala
final class Counter:
  private var count = 0
  def bump(): Unit = count = count + 1
```

```coq
Definition bump : tree mem unit := x <~ Get ;; _ <~ Put (S x) ;; Ret tt.
```

| Part | In the example |
|---|---|
| Execution | Two operations, a read and a write. The addition is a term. |
| Values | The number read, `x`. |
| Vocabulary | Memory (`mem`, with operations `Get` and `Put`). The definition contains no thread or monitor operation. |
| Statements | A read gives the stored number. A write stores the number written. These are stated outside the definition. |
| Concurrent execution | See below. |

Three claims are proven about this definition (3.9):

- Executed alone, it adds one.
- Two concurrent executions can end with one added (both read before either writes).
- Two concurrent executions, each between entering and leaving a monitor, end with two added.

### 2.5 Properties

- A proof refers only to the vocabularies of its program and their laws. A proof about cats-effect code that
  accesses no field does not refer to objects.
- A proof uses a lower layer only at the operations where the code uses that layer.
- The translation produces one definition per method. All proof methods of 3.10 apply to that definition.

## 3. Model

### 3.1 Programs

```coq
Inductive tree (E : Type -> Type) (A : Type) : Type :=
  | Ret (a : A)
  | Vis (X : Type) (e : E X) (k : X -> tree A)
  | Iter (St B : Type) (body : St -> tree (St + B)) (s : St) (k : B -> tree A).
```

- `E` is the vocabulary. `E X` is the type of operations with result type `X`.
- `Ret a` gives `a`.
- `Vis e k` performs `e` and continues with `k` applied to the result. `k` is a function of the prover. Pure
  computation between operations is inside `k`.
- `Iter body s k` is a loop over a state. One iteration, `body s`, gives either the next state or the result
  of the loop. The loop then continues from the next state, or continues with `k` applied to the result.
- The type is inductive. Structural recursion and induction over programs are available.
- `bind` sequences two programs. The laws `bind_ret` and `bind_bind` are proven, assuming function
  extensionality.

Exceptions. A program that may throw has result type `exn + A`: `prog E exn A := tree E (exn + A)`. The
following are functions on programs: `throw`, `then_` (sequencing that stops at a throw), `try_catch`,
`try_finally`, `loop`. The laws `ret_then`, `then_ret` and `then_then` are proven, assuming function
extensionality.

Status: built (`FrFlow/Effect/Tree.v`).

### 3.2 Values

| Scala | Value in the prover |
|---|---|
| `Int` | An integer. Arithmetic operations wrap to 32 bits as on the JVM. |
| `Boolean`, `Unit` | `bool`, `unit`. |
| case class, enum | An inductive type. |
| object | A reference. The type of references has an equality test and no other structure. |
| lambda, by-name argument | A function value (3.3). |
| value of a library type, such as `IO[A]` | A value of a type declared by the library's vocabulary, with the functions that build it (3.4). |

- The location of an object is not part of the model. It exists only in a model of the memory vocabulary
  (3.7).
- Classes, fields and methods are named by generated types with one constructor per class, per field and per
  method. The type of a field's content is a function of the field's name.
- Subtyping, variance, path-dependent types and givens are resolved by the Scala compiler before translation.
  They determine which program is produced and are not represented in it.

Status: integers, booleans, references and names are built. Two deviations: the reference type is concrete
(4.6), and integer inputs of a method are not restricted to 32 bits (5.5). Inductive types, function values
and library values are designed.

### 3.3 Function values and method calls

Function values.

- A lambda is translated to a function value constructed from its captured values.
- Applying a function value is an operation. Its definition, for a given lambda, is the program of the
  lambda's body.
- A function value does not contain a program. In the prover, a program cannot be the result of an operation
  or the content of a field (a universe constraint). A program can be an argument of an operation, such as
  the body given to an operation that starts a fiber.

Method calls.

- A call is an operation on a reference. Its definition is the program of the method.
- A method has a specification: a precondition and a postcondition. The specification is a law about the call
  operation. A proof about a caller uses the specification of the callee. Each method's program is proven to
  satisfy its specification.
- Without specifications, a proof about a caller unfolds the callee's program. This does not terminate for
  recursive methods.

Pure arguments. Where a library requires a pure function, the operation takes a function of the prover. For
example, cats-effect may apply the function passed to `Ref.modify` more than once. A lambda that performs an
operation cannot be translated to a function of the prover. The translation rejects such code.

Status: calls and their definitions are built (the `body` table). A lambda as a function value is on an
example (3.4). Specifications are designed.

### 3.4 Deferred values

With cats-effect or ZIO, Scala code builds a value that is executed later by the library. The model has no
separate notion of execution for this.

- Functions that build such a value are functions on values. `IO.pure(a)` and `io.flatMap(f)` return a value
  and perform no operation.
- Executing such a value is an operation, `Run`. Laws specify it. `Apply f x` is the operation that applies a
  function value. Type arguments are omitted:

  ```coq
  Run (io_pure a)        ~~  Ret a
  Run (io_flatMap io f)  ~~  x <~ Run io ;; next <~ Apply f x ;; Run next
  ```
- Arguments are evaluated by Scala's rules. `IO.pure(next())` calls `next()` when the value is built.
  `IO.delay(next())` places the call in a function value.
- A value of type `IO[IO[A]]` is a value that contains a value. No additional construct is needed.

Example.

```scala
def read(io: IO[Int]): IO[Int] = io.flatMap { x => seen = seen + 1; IO.pure(x) }
```

`read` builds a value and performs no operation. Its lambda is the function value `read_1 this`. The
definition of applying it is the lambda's body:

```coq
Apply (read_1 this) x  ~~  seen <~ Load this ;; _ <~ Store this (S seen) ;; Ret (io_pure x)
```

The following is proven from the two laws and this definition (`running_read`):

```coq
Run (io_flatMap io (read_1 this))  ~~  x <~ Run io ;; seen <~ Load this ;; _ <~ Store this (S seen) ;; Ret x
```

The sequence on the right is derived by rewriting. The translation does not assume it.

Status: on an example. The library contains no library vocabulary.

### 3.5 Vocabularies

A vocabulary is a family of operations indexed by result type.

| Vocabulary | Operations |
|---|---|
| memory | read a field, write a field, create an object |
| calls | call a method of the translated code |
| function values | apply a function value |
| monitor | enter, leave |
| cats-effect `Ref` | `get`, `set`, `modify` with a pure function |
| library values | run a value |
| fibers, threads | start a body, join |
| external system | one operation per member that is called |

Sums. A program over two vocabularies is a program over their sum. Each operation is tagged as belonging to
the first (`inl1`) or the second (`inr1`). In the example of 2.4, `bump` is over memory. The guarded program
contains `bump` between the monitor operations. `within` maps a program over memory to the same program over
the sum:

```coq
Definition guarded : tree (sum1 monitor mem) unit :=
  _ <~ inl1 Lock ;; bind (within bump) (fun _ => _ <~ inl1 Unlock ;; Ret tt).
```

Rules.

- A program is over exactly the vocabularies that its source code uses.
- A proof about a program may use the laws of those vocabularies only.
- An operation that takes a program as an argument records the vocabulary of that argument. For example,
  `Par a b` (run two bodies concurrently) is typed by the vocabulary of `a` and `b`. A law stated for bodies
  over one vocabulary does not type-check against a body over a larger one.

Status: the library has a single vocabulary containing memory, calls and external calls. Separate
vocabularies, sums and argument vocabularies are on an example.

### 3.6 Statements

| FrFlow | Model |
|---|---|
| declaration | operation |
| assumption | law that is not proven |
| claim | proven law, or proven property of a program |
| definition | meaning of an operation as a program over other vocabularies |

A law has one of three forms:

- An equivalence between programs. Example: two consecutive updates are equivalent to one update with the
  composed function.
- A relation between an operation, the state before it and the state after it. Example: a monitor can be
  entered only when no thread holds it.
- A specification of a method (3.3).

A definition gives an operation a meaning in a lower layer. A method call is defined by the method's program.
A cats-effect `Ref` can be defined as a field that holds an `AtomicReference`.

Scope of a law. A law applies to programs over its own vocabulary. It does not apply to a program that
contains operations of another vocabulary. To reorder an operation of one vocabulary with an operation of
another, a law stating their independence is required.

Status: designed as part of FrFlow. Laws of the first two forms, and claims proven from them, are on an
example.

### 3.7 Models

A model of a vocabulary assigns a concrete behaviour to each operation such that the laws of the vocabulary
hold. A model is used for three purposes:

- Consistency. If a set of laws has a model, the laws are consistent.
- Testing. An executable model runs a program. The result is compared with the result on the JVM.
- Discharging a layer. A law that is assumed at one layer is proven in a model defined in the layer below.

A proof of a claim at a layer does not use a model.

The executable model of memory represents the heap as a list of objects. The following exist only in that
model:

- A reference is an index into the list.
- Execution takes a step bound (fuel), because functions of the prover must terminate. If an execution ends
  within a bound, it ends with the same result for every larger bound (`run_more`, proven).
- An execution can be stuck. This is the result of an access that the laws do not cover, such as an access
  through `null`.

Status: the executable model is built (`FrFlow/Effect/Run.v`). The laws of memory are not yet stated, so the
proof that the model satisfies them is designed.

### 3.8 Program equivalence

Two syntactically different programs can have the same behaviour. Equality of the prover does not relate
them. The model uses an equivalence relation, written `~~`. It has two definitions.

Definition at a layer. `~~` is the least relation that is an equivalence, is preserved by sequencing on
either side, and contains each law of the layer's vocabularies. This definition is inductive and refers to no
model.

Definition in a model. Two programs are equivalent if, in every context, they produce the same set of results
and final states. A context places a program before, after, or concurrently with the two programs.

Soundness. A model satisfies a vocabulary if each of its laws holds under the second definition. In that
case, every equivalence derivable under the first definition holds in the model. This is proven once per
model.

Notes.

- Concurrent contexts make some laws conditional. `bump` and a single atomic increment have the same results
  when executed alone, and different results when another thread executes concurrently. A law that holds only
  when no other program accesses the same state must state that condition. The cats-effect laws of 3.9 are
  stated for a `Ref` that only the program under proof accesses.
- A root claim should be stated about results: every execution of the program ends in a state with a given
  property. `~~` is used for rewriting within proofs.
- For nondeterministic programs, refinement is used: every result of one program is a result of the other.
  Two updates that do not commute, executed concurrently, refine the choice between the two orders. They are
  not equivalent to either order.

Status: the definition at a layer is on an example (`same`, `adds_two`). The definition in a model and the
soundness theorem are designed.

### 3.9 Concurrent execution

Concurrent programs are interleaved at operations. One program cannot observe or affect another between two
operations of that other program.

Rule for the translation. Each operation on state that another thread can access is a separate node. The
translation does not merge operations. A local variable is translated to a value unless a lambda captures
it. This is correct because no other thread can access an uncaptured local variable.

Cases. The applicable case is determined by the program:

1. The program has no operations. Interleaving has no effect. Every sequential proof holds.
2. The program has operations on state that no other program accesses. The sequential laws hold once this is
   proven.
3. The program has operations on shared state. The sequential laws do not apply.

Conditions on laws. The law of memory is that a read gives the most recent write. For a program executed
alone, the most recent write is its own. Under concurrent execution it may be another program's. The law of a
monitor provides mutual exclusion, under which the sequential reading holds again.

JVM. Interleaving of reads and writes is the semantics of a field that is `volatile`, or that is accessed
without a data race. For a non-volatile field with a data race, the JVM permits additional behaviours
(JLS 17.4). The JVM layer must either prove the absence of data races, as the Ox proofs do, or make no claim
about such a field. A lost update is among the behaviours the JVM permits.

Example: threads. `ends law a b s x y s'` states that `a` and `b`, executed concurrently from state `s` under
the laws `law`, can both terminate with results `x` and `y` in state `s'`. `many alone c c'` states that a
single thread reaches `c'` from `c`. Under `stores` (memory) the state is the number. Under `jvm` (memory and
a monitor) the state is the number and the thread that holds the monitor, if any.

```coq
Lemma   bump_alone_adds_one n : many alone (bump, n) (Ret tt, S n).
Lemma   bump_loses_one : ends (fun _ => stores) bump bump 0 tt tt 1.
Theorem guarded_counts_both x y s' : ends jvm guarded guarded (0, None) x y s' -> s' = (2, None).
```

The theorem is proven with an invariant over all interleavings: the number equals the sum of what each thread
has added. The invariant is stated in terms of each thread's position in its program.

Example: cats-effect. The program is `(ref.update(_ + 1), ref.update(_ + 1)).parTupled *> ref.get`. Three
laws are assumed for a `Ref` that no other program accesses:

- Two updates executed concurrently are equivalent to the two updates in sequence, if the functions commute.
- Two consecutive updates are equivalent to one update with the composed function.
- A read after an update is equivalent to the update after a read, with the function applied to the value
  read.

The claim is proven by three rewriting steps. It does not refer to threads or objects:

```coq
Theorem both_then_read_adds_two :
  both_then_read ~~ bind read (fun x => bind (update (fun n => S (S n))) (fun _ => Ret (S (S x)))).
```

Lower layer. If an update is a single operation, the first law's statement about final states is a theorem
of the interleaving (`par_updates_holds`): the final content of the `Ref` is the content after one of the two
orders. A read followed by a set is two operations. The law does not apply to it, and it is proven that two
concurrent executions can lose an update (`read_then_set_loses_one`).

Status: on an example, for two programs without loops. Interleaving of an arbitrary number of programs, and
the theorem that lifts a sequential claim to concurrent execution under non-interference, are designed.

### 3.10 Proof methods

A proof at a layer does not execute the program and does not refer to fuel. The tests of 4.7 do both.

| Program construct | Method |
|---|---|
| sequence of operations | One step per operation, using a law of that operation. |
| loop | An invariant over the loop state. The state consists of the variables assigned in the Scala loop. |
| call | The specification of the callee. |
| library operations | Rewriting with the laws of the library. |
| concurrent programs | An invariant over all interleavings, or laws about concurrent composition. |
| termination | A measure that decreases with each iteration. |
| ownership | A separation logic with one rule per operation. |

Status: the Ox proofs use the first and fifth methods over an earlier representation (`step`, `pass`). For
the representation specified here, the methods exist only as used in `Worked.v`. General rules, their
soundness, and the separation logic are designed.

## 4. Implementation

The code uses different names for three terms of this document:

| This document | Code |
|---|---|
| vocabulary | `eff` |
| operation | effect |
| program | `tree`, `prog` |

### 4.1 Pipeline

```text
Scala source
   │  scalac
   ▼
class file ───────────────► JVM                     (reference for tests)
TASTy
   │  stage 1: normalisation                        (designed)
   ▼
normalised Scala (4.2)
   │  stage 2: evaluation, `frflow.dsl.compiled.effect`
   ▼
program representation (4.3), `frflow.core.effect.Program`
   │  printer, `frflow.proof.effect`
   ▼
Rocq file over `modules/proof/rocq/FrFlow/Effect`
```

Requirements on the stages:

- Each representation is plain data. It does not refer to the Scala compiler or to a prover.
- Stage 1 depends on the Scala compiler interface. Stage 2 and the printer do not.
- The printer depends on the syntax of one prover. Output for another prover is another printer over the same
  program representation.
- A construct that a stage does not translate is rejected with its file and line. It is not omitted or
  approximated.

Status: stage 1 and normalised Scala are designed. The implemented emitter performs both stages in one pass
over TASTy (4.4). No other part of FrFlow uses the output. The Ox model and `lifted[Class]` structures use
earlier representations ([EXECUTIONS.md](EXECUTIONS.md), [LIFTED.md](LIFTED.md)).

### 4.2 Normalised Scala

Normalised Scala is the code after the rewrites that Scala's definition prescribes, and before any
interpretation. It has the role of Charon's LLBC for Rust.

Properties:

- Typed. Each local, parameter, field and method has a type. Each reference to a class, field or method is
  resolved to its name.
- Statement form. A method body is a block of statements. A local `var` is assigned by a statement. Locals
  are not replaced by values.
- Explicit evaluation order. The operands of a call, an operation or a field access are atoms: a local, a
  literal, or `this`. Each intermediate result is bound to a local.
- Executable. The representation has an interpreter written in Scala, used for testing (4.7).

Grammar:

```text
class   ::= name, fields, methods, initialiser
method  ::= name, parameters, result type, block
block   ::= stmt* atom
stmt    ::= val x = rhs
          | var x = atom                               declaration of a local var
          | x = atom                                   assignment to a local var
          | atom.f = atom                              field write
          | while (block) block
          | return atom
          | throw atom
rhs     ::= atom
          | primitive(atom*)
          | atom.f                                     field read
          | new C
          | call(kind, atom, m, atom*)
          | closure(code, atom*)                       code name and captured values
          | apply(atom, atom*)
          | isInstance(atom, C) | field(atom, i)       tests and projections for matching
          | initialise(O)                              object or lazy val, once
          | if atom then block else block
          | try block catch (x) block finally block
atom    ::= local | literal | this
kind    ::= static(m) | virtual(m) | external(m)
```

Normalisation is a sequence of passes. Each pass maps normalised Scala, or TASTy for the first, to normalised
Scala with one construct removed:

| Pass | Removes | Produces |
|---|---|---|
| N1 | nested expressions with operations | bindings to locals, in evaluation order |
| N2 | `&&`, `\|\|` with an operation on the right | conditionals |
| N3 | `match` | `isInstance`, `field`, conditionals; `throw` of `MatchError` |
| N4 | lambdas | `closure` with the captured locals; the body as a named code unit |
| N5 | captured `var`s | a cell object, with field reads and writes |
| N6 | by-name arguments | closures |
| N7 | calls | the call kind: static, virtual with the declared method, or external |
| N8 | `lazy val`, `object` references | `initialise` |
| N9 | `return` inside nested blocks | a structured exit of the method |

Requirement: a pass preserves the result of the interpreter on every test program.

Status: designed. The repository has a reader for TASTy that the Ox proofs use
(`frflow.dsl.compiled.source`). It preserves the structure of TASTy, resolves names, and writes untyped data
for the Rocq type `FrFlow/Scala/Tree.v`. It performs none of the passes above and has no interpreter.

### 4.3 Program representation

The program representation is the result of stage 2. It has the role of the output of Aeneas for Rust, with
one difference: operations on objects remain, because Scala does not exclude aliasing.

| Part | Contents |
|---|---|
| `Program` | source class names, class names, fields, methods, external members |
| `MethodOf` | name, inputs with types, result type, body |
| `Tree` | `Give` a value; `Do` an effect and continue; `Name` a value; `Branch`; `After` (run a tree, bind its results); `Loop`, `Again`, `Leave` |
| `Effect` | `Get`, `Put`, `New`, `Call` with its receiver, `Ext` |
| `Pure` | local name, integer, boolean, unit, null, primitive applied to arguments, conditional term, tuple |
| `EType` | `Int`, `Bool`, `Unit`, `Ref`, tuple |

Properties:

- A local is a value. There is no assignment.
- Pure computation (`Pure`) is separate from operations (`Effect`).
- The state of a loop is explicit.

Planned extensions, in the order of 5.4:

| Extension | For |
|---|---|
| the vocabularies of each method; each effect tagged with its vocabulary | 3.5 |
| code units for lambdas, with captured values; an `Apply` effect | 3.3 |
| inductive type declarations; a match on constructors in `Pure` and `Tree` | 3.2 |
| `Throw` and `Try` nodes | 3.1 |
| applications of pure library functions in `Pure` | 3.4 |

Laws and specifications are not part of the program representation. They are FrFlow statements about its
names.

Status: built (`frflow.core.effect`), without the extensions.

### 4.4 Evaluation

Stage 2 evaluates each method symbolically. It maintains, for each variable in scope, the variable's current
value as a term.

- A local `val` or `var` is represented by its current value. An assignment to a `var` replaces the value. No
  memory operation is emitted.
- A conditional whose branches assign variables gives the values of those variables together with its own
  value.
- The state of a loop is the set of variables assigned in its condition and body.
- Operations are emitted in evaluation order.
- Bound names in the output are the names used in the source.

The implemented emitter applies these rules to TASTy directly:

| Scala | Output |
|---|---|
| literal, `this`, local variable, parameter | term |
| `+`, `-`, `*`, comparisons, `!`, `==` on `Int` or `Boolean` | term (`iadd a b`, `a <? b`, …) |
| `a && b`, `a \|\| b` | term if `b` has no operation, otherwise a conditional |
| `val x = e`, `x = e` on a local variable | output of `e`; the value is bound to `x` |
| `o.f`, `o.f = e` | `get o F`, `put o F v` |
| `o.c` where `c` is a `final val` with a literal type | the literal |
| `o.m(a, b)`, `m(a, b)` on translated code | output of `o`, `a`, `b` in that order, then `call o M (a, b)` |
| `o.m(a, b)` on other code, with `o` written | `ext O (o, a, b)` |
| `new C(a)` | `new C_C`, output of `a`, `call c M_C_new a` |
| `a eq b`, `a ne b` of `Object` | term |
| `if` with operation-free branches | terms |
| `if` otherwise | conditional that gives its value and the assigned variables |
| `while c do b` | `loop` over the assigned variables |
| constructor | method `new`: writes each parameter that is a field, then the class body in order |

Section 5.1 lists the rejected constructs.

Example of output, for a method with two `var`s and a `while`. `prog Z` is a program whose result is an
integer or an exception. `x <- p ;; rest` sequences programs. `again` and `leave` end an iteration. `iadd` is
addition with wrapping. The output contains no memory operation:

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

Status: built for the constructs in the table, as a single pass that also performs the part of N1 and N2
those constructs need.

### 4.5 Generated file

The printer produces one file per program. It contains:

- the types of class, field, method and external names;
- the typing tables: the content type and class of each field, the class, input type and result type of each
  method;
- one definition per method;
- the table `body`, from a method name to its program.

`modules/project/src/test/resources/effects/Samples.v` is the output for the test classes. It is stored in
the repository and compared with the emitter's output on each test run.

### 4.6 Prover library

| File | Contents |
|---|---|
| `Tree.v` | Programs, sequencing and its laws, exceptions, loops. |
| `Int32.v` | `Int` as an integer (`Z`) with wrapping arithmetic. |
| `Sig.v` | The single vocabulary (`Get`, `Put`, `New`, `Call`, `Ext`), typed by the generated names. The reference type `null \| at_ n`. |
| `Run.v` | The executable model: objects, execution with results `Gave`, `Stuck`, `Spent`, and `run_more`. |

Section 5.2 lists the differences between the library and section 3.

### 4.7 Tests and trust

Tests.

- Comparison with the JVM (`EffectRunSuite`). Nine scenarios are executed on the JVM and, as emitted programs,
  in the executable model with fuel. Rocq proves each pair of results equal by computation. The scenarios
  cover fields, aliasing, calls, nested loops, a loop condition with an operation, conditionals that assign,
  integer wrapping, evaluation order, a field and a constant read before initialisation, a variable assigned
  in a receiver expression, overloads, and user methods named `eq`. Two lemmas state that a call on `null`,
  and a call on an object of another class, are stuck.
- Stored output. The generated file for the test classes is compared on each run.
- Rejections. Ten rejected constructs are tested.
- Printer. Tested on a hand-built program.
- Worked examples. `Worked.v` contains everything section 3 marks as on an example.

Planned tests for the two-stage pipeline (designed):

- Stage 1. The interpreter of normalised Scala is compared with the JVM on the test programs. Each pass is
  tested by running the interpreter before and after it.
- Stage 2. The executable model of the program is compared with the interpreter of normalised Scala, in
  addition to the JVM.
- Normalised Scala can be printed for the prover with a meaning defined there. The correctness of stage 2 can
  then be stated in the prover as a relation between that meaning and the program.

Limits.

- The emitter and the printer are tested and not proven correct. A review of the first version found eight
  classes of accepted Scala whose program differed from the JVM while all tests passed. Each is now rejected
  or translated correctly, with a test.
- The tests compare the final results of single-threaded executions.
- There is no proven relation between these programs and the earlier representation.
- Normalised Scala and its interpreter do not exist, so the two stages are tested together.
- TASTy contains the code as typed, before inlining and erasure. The emitter rejects constructs that those
  phases change.
- The worked examples are hand-written programs over a single number. They are not emitter output and
  contain no objects.

## 5. Coverage

### 5.1 Scala

Translated:

- final classes with fields, primary and secondary constructors, and methods;
- `Int`, `Boolean`, `Unit`;
- any object type as a reference, including types that are not translated (`String`, arrays); methods of such
  types are external calls;
- `if`, `while`, `&&`, `||`, local `val` and `var`, field reads and writes, `new`;
- calls of translated code and of external code.

Rejected, with the planned translation:

| Construct | Planned translation |
|---|---|
| lambdas, by-name arguments | function values (3.3) |
| case classes, enums, `match` | inductive types |
| `throw`, `try`, `finally`, `return` | the functions of 3.1; emission is not implemented |
| objects, `lazy val` | an initialise-once operation |
| `synchronized`, threads | monitor and thread vocabularies (3.9) |
| cats-effect, ZIO | library vocabularies (3.4) |
| other numeric types, `Char`, `/`, bit operations, other literals | a value type and operations for each |
| traits, inheritance, non-final classes, dynamic dispatch | open (5.5) |
| generic classes and methods | open (5.5) |

Rejected, with no planned translation: `inline` methods and fields, repeated parameters, nested classes and
methods, type members, casts, `==` on objects, an external call without a written receiver, a setter called
by name, a conditional between two value types whose value is used, and two entities that would receive the
same name in the generated file.

### 5.2 Model

| Part | Status |
|---|---|
| programs, sequencing, exceptions (3.1) | built |
| integers, references, typed names (3.2) | built; reference type is concrete; integer inputs are unbounded |
| calls defined by the method's program (3.3) | built |
| executable model; fuel confined to it (3.7) | built |
| program representation; evaluation of the constructs of 4.4 (4.3, 4.4) | built, in one pass over TASTy |
| normalised Scala, its passes and interpreter (4.2) | designed |
| function values; deferred values (3.3, 3.4) | on an example |
| separate vocabularies, sums, argument vocabularies (3.5) | on an example; the library has one vocabulary |
| equivalence at a layer (3.8) | on an example |
| concurrent execution: one definition alone and concurrent, monitor, cats-effect laws, one law in a lower layer (3.9) | on an example; two programs, no loops |
| laws of memory; proof that the model satisfies them (3.6, 3.7) | designed |
| method specifications; rules for steps and loops (3.3, 3.10) | designed |
| equivalence in a model; soundness (3.8) | designed |
| lifting of sequential claims to concurrent execution (3.9) | designed |
| separation logic (3.10) | designed |

### 5.3 Proof kinds

| Proof kind | Provided by the model | Status |
|---|---|---|
| library laws | library operations with laws; rewriting; no reference to objects | on an example |
| JVM | interleaving of the same programs under JVM-level laws | on an example; the Ox proofs are not migrated |
| induction | inductive programs, loop invariants, specifications | designed |
| separation logic | one rule per operation over the same programs | designed |

### 5.4 Order of work

Each step can be used independently of the later ones.

1. Make the reference type abstract. Keep indices inside `Run.v`.
2. Split the vocabulary into memory, calls and external calls. Add sums. Stage 2 computes the vocabularies
   of each method.
3. State the laws of memory. Prove that the executable model satisfies them.
4. Rules for steps and loops, method specifications, and their soundness.
5. Normalised Scala for the constructs translated today, with its interpreter. Stage 2 reads it instead of
   TASTy.
6. Passes N4 to N6 and function values in the program representation.
7. Passes N3, N7 to N9; inductive types, exceptions and dispatch in the program representation.
8. Library vocabularies, starting with cats-effect: building functions, `Run`, laws.
9. Interleaving of an arbitrary number of programs, the lifting theorem, and migration of the Ox proofs.
10. Equivalence in a model and the soundness theorem of 3.8.

### 5.5 Open questions

- Dispatch and typed `catch` require the class of an object. The class can be obtained by an operation of a
  separate vocabulary, or stored in the reference.
- Exceptions raised by the JVM, such as `NullPointerException`. Either operations can fail, or the emitter
  emits a test before each access.
- Integer range in Rocq. Method inputs are arbitrary integers. Universally quantified statements are sound.
  Existential statements about inputs are not, until inputs are restricted to 32 bits.
- Generics. The typing tables map a name to a type and have no type parameters.
- Monitor re-entry. The law in the worked example does not permit re-entry. JVM monitors do.
- Field modifiers (`volatile`, `final`) are not recorded. The JVM layer requires them.
- Other provers. The representation does not depend on Rocq. Output for Lean requires a second printer.

## References

- Charon and Aeneas (Rust). Charon produces LLBC, a normalised, typed, statement-level form of a Rust crate
  with structured control flow and explicit trait resolution. Aeneas evaluates LLBC symbolically and produces
  pure functions for a prover. Normalised Scala (4.2) corresponds to LLBC. The program representation (4.3)
  corresponds to the output of Aeneas, with operations on objects retained.
- Plotkin and Power, algebraic effects: operations with equations form a theory; a model is an interpretation
  that satisfies the equations.
- Interaction trees, and "Program Logics à la Carte": programs as trees over a signature of operations; one
  program logic per signature.
- DOT and gDOT: Scala's types are not embedded in the prover's type system.
