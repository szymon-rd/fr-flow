# Thread programs read from TASTy

FrFlow reads compiled Scala that calls the JDK's concurrency classes into the Rocq language of
`modules/proof/rocq/FrFlow/Threads/Lang.v`, by rules over Scala's constructs. Nothing is compiled or run: the
trees are read from the `.tasty` files of a jar or a directory (`frflow.dsl.compiled.Inspect`).

The first unit read is Ox 1.1.0's scopes and forks: `examples/ox/rocq/Ox/Gen.v` is generated, `Code.v` beside it
is the same unit written by hand, and `Agree.v` (generated) states that the two agree.

## Where it is

| What | Where |
|---|---|
| The language read into: terms, types, declarations, a file | `modules/core/…/frflow/core/threads` (`Term`, `Ty`, `Decl`, `Draft`, `Program`) |
| Laying a unit out as a file: order, closures, what it mentions | `core.threads.Assemble`, `core.threads.Closures` |
| The tables | `modules/dsl/…/frflow/dsl/compiled/threads/known` (`ThreadUnit`, `Jdk`, `JdkOp`, `Thrown`, `Reserved`) |
| The reader, one trait for a rule or a few | `frflow.dsl.compiled.threads` and `.reading` (`ReadThreads` is the entry) |
| The printer of the file, and of the agreement | `modules/proof/…/frflow/proof/rocq/threads` (`RocqThreads`, `RocqAgreement`) |
| Ox's unit, and the suite | `modules/project/src/test/…/frflow/project/rocq` (`OxUnit`, `OxThreadsRocqSuite`) |

```bash
sbt "project/testOnly frflow.project.rocq.OxThreadsRocqSuite"         # generates, compares with Gen.v and Code.v
sbt "project/Rocq/testOnly frflow.project.rocq.OxThreadsRocqSuite"    # compiles Gen.v and Agree.v with Rocq
FRFLOW_ROCQ_WRITE=1 sbt "project/testOnly frflow.project.rocq.OxThreadsRocqSuite"   # writes Gen.v and Agree.v anew
```

## The rules

No rule names a method of the code read. What a rule does not cover is refused, and what holds the refused
construct is `chaos` (see "What is not read").

### Types (`ReadTypes`, `ReadShapes`)

| Scala | Rocq |
|---|---|
| a class of the unit | `Record C := mkC { C_f : T; … }`: its fields are the constructor's parameters and the `val`s, in order |
| a class with a field of its own type (`parent: Option[…]`) | `Inductive C := mkC (f : T) …`, and a function `C_f` for each field |
| a trait of the unit, sealed (its children) or with its cases named | `Inductive S := \| S_A \| S_B (x : B) …`: an object is a constant, a class of the unit is held |
| a trait with parameters that is a case of a sum | `S_A (param : T) …`: it holds its parameters, and its methods are the sum's |
| a trait that one class of the unit extends, and no other | that class (`OxUnsupervised`, `Ox` and `ResourceScope` are `OxError`) |
| a class that extends a class of the unit | that class |
| a class of `Jdk.types` | what the table says: a `Thread` is `tid`, an object with state a reference (`nat`) |
| a `Throwable` | `exn` |
| a class of the unit's `opaque` | a handle, `nat` |
| `Option[A]`, `List[A]`, `Either[A, B]` | `option A`, `list A`, `A + B` |
| a `Set[Thread]` held in a variable | `list tid` (`tset_contains`, `tset_add`) |
| a by-name type, a function type, a context function type | `code` |
| a type parameter, an applied type parameter (`F[T]`), a union | `val` |
| `Nothing` | `Empty_set`; as a parameter, `val` |

A class with a `var` field is refused: a record's fields do not change.

`obj` has a case `O_C (x : C)` for each public class of the unit (a caller's data may hold one), then one for
each other thing the code puts where a `val` is, in the order they are first mentioned. An enum case or an object
of a class that is not read is a constant `O_<owner>_<name>`.

### Definitions (`ReadSigs`, `ReadClasses`)

- Method `m` of a class read as `C` is `C_m (this : C) …`; of an object `O`, `O_m …`; a top-level method keeps its
  name. Of the methods of one name that an owner declares in its source, each is numbered in order (`m_1`, `m_2`).
- The parameters are those of every list, in the source's order, `using` ones included. One the source does not
  name is `x1`, `x2`, …. `summon[T]` arrives in TASTy as that parameter.
- Every body is a program, `M T`. A field is `C_f this`; a method of a case that holds its parameters starts
  `let (params) := this in`.
- The constructor of `C` is `C_new`: it runs the fields' initialisers in order, then `ret (mkC …)`. A case class's
  synthetic `apply` is `mkC`. A constructor is refused if the class extends one whose constructor runs code.
- A sum's method `S_m` matches on `this` and calls the case's method.
- A group's definitions keep the order of the unit's table, but each is written after those of the group it calls:
  the group is passed over in order, as many times as it takes, each pass writing what calls nothing unwritten.

### Statements (`ReadBlocks`)

- `val x = e` is `x <- e ;;` where `e` is a program and `let x := e in` where it is a value. A `val` that only
  names a variable of the same name is that variable.
- `x` is bound at the type it is declared with. A value read at another type is cast, each step binding `x` again
  (`fs <- unnull fs ;; fs <- cast_list fs`).
- A statement whose value is not used is `_ <- e ;;`; one that is a value is not written. The statements of an
  inner block are written among the outer ones where they bind no name in scope.
- An effect inside an expression (an argument, a condition, a scrutinee) is run before the statement the expression
  is in, in Scala's order of evaluation, and what it gives is named: `x` (`e` for an exception) where there is one
  effect among the arguments of a call, `x1`, `x2`, … where there are several. A name is passed over if a variable
  in scope has it, or if it would hide something still to be read.
- `if c then return v`, then the rest, is `if c then v else` the rest. Any other `return` is refused.

### Null (`ReadBlocks`, `ReadMatch`)

A value that may be null (what `ThreadLocal.get` and `AtomicReference.get`/`getAndSet` give, the literal `null`)
is an `option`; `Option(x)` of one is itself.

- A `val` bound to one and tested for null is held as an option under a new name. `if v == null then a else b` is
  `match x with None => a | Some v => b end`: `v` names the value in `b`, cast to its class where it was held as a
  `val`. `e match { case null => a; case v => b }` is the same.
- A `val` that is only given on where a null may be (an argument of an operation that takes one) keeps the option.
- A `val` read first thing after it is bound, where a null is no value, is `unnull` as it is bound (nothing
  happens between). Any other is `unnull` where it is read.
- A `var` initialised with `null` is an option under its own name. Where it is tested, a new name (`e` for an
  exception, else `x`) names what it holds.
- `null` and an empty list are written with their types (`(@None exn)`, `(@nil tid)`), except as an argument of a
  constructor, an operation or a definition, whose parameter gives the type (`None`, `[]`).

### Control (`ReadControl`, `ReadMatch`)

- `if`: Rocq's, each branch a program. `a || b` with an effect in `b` is `if a then ret true else b`.
- `try a catch cases` is `try_catch a (fun e => match e with … end)`. A case is a constructor of `exn`
  (`Thrown.classes`), with what its methods read bound by the pattern (`ExecutionException cause`, for `getCause`);
  a case for `Throwable` is `| _ =>`; what no case takes is thrown again (`| _ => throw e`). One case for
  `Throwable` is the handler itself, with no `match`. A guard, or a class `exn` has no constructor for, is refused.
- `try a finally f` is `try_finally a f`. `throw e` is `throw e`.
- `match` on an `Option` or an `Either` is Rocq's on `option` or a sum (`Left` is `inl`, `Right` is `inr`), one arm
  for each constructor, in the order the cases first name them. A case with a guard is `if guard then … else` the
  next case that takes the same constructor.
- `e match { case _ => b }` (what `val _ = e` compiles to) evaluates `e`, then `b`.

### Variables and loops (`ReadVars`, `ReadDefs`, `ReadUses`)

- `var x = e` is `let x := e in`. Whatever assigns `var`s gives their new values (one: the value; several: a tuple
  `st`, in the order they are declared), and what follows binds their names again (`let (a, b) := st in`).
  A construct read for the `var`s it assigns pushes them into its branches; an assignment that ends a branch is
  `ret` of the new values, and a program that gives the one new value is that program.
- `while c do b` is `while (fun st => c) (fun st => b) st`, `st` the `var`s the loop assigns: one is passed under
  its own name, several as `st`, taken apart where the function reads them.
- A local method is `let f := fun params => body in` (no parameter: `let f := body in`). The `var`s it reads or
  assigns are its first parameters, and it gives the new values of those it assigns.
- A local method that calls itself (`@tailrec`) is `loop` over its parameters: a call of itself is `ret (inl
  arguments)`, any other end `ret (inr result)`.

### Functions as values (`ReadClosures`, `core.threads.Closures`)

- A by-name parameter, and a parameter of a function type, is a `code`. Reading a by-name parameter is `invoke f
  VUnit`; applying a function is `invoke f arg`, the argument held as a `val`.
- A lambda or a by-name argument given to code that keeps it (a definition of the unit, `newThread`) is a
  constructor of `code`, `Lam_<definition>_<n>`, over the variables it captures; what it runs is the definition
  `Lam_<definition>_<n>_body`, over those variables and `arg`, and a case of `interp`. It gives a `val` (`VUnit`
  for `Unit`). The closures of the definitions of one name are numbered in the order they are written, one inside
  another after it. The captured variables are listed in the order the enclosing definition's earlier statements
  mention them, then in the order the closure's own body does.
- A closure in scope given on (`f`, or `x => f(x)`) is that closure.
- A lambda given to a traversal is a Rocq function. A concurrent set's `forEach` is `TsForEach`, `EsForEach` or
  `VsForEach` by what the set holds; the function takes the element and the `var`s the lambda assigns, and gives
  them back (`tt` when there are none). A list's `foreach` is `List_foreach`.
- A parameter the compiler named (of an eta-expansion, of `_`) is `x`.
- A closure that reads or assigns a `var` is refused.

### Calls (`ReadCalls`, `ReadOps`, `ReadData`, `ReadInline`)

By what is called, in this order:

1. `throw`.
2. A local method.
3. A method with no argument that reads a field: `C_f x`.
4. A definition of the unit: its name applied, `this` first. A trait's method called on a value read as a class
   is that class's method.
5. An `inline` method. TASTy holds the call, not its expansion, so the call is read as the method's body, in the
   scope of the call: an `inline` or by-name parameter is its argument, read where the parameter is; any other
   parameter is the argument's value. A call whose body is not read is `chaos` named for the method.
6. A method of the JDK: `call` of its operation (`Jdk.methods`), the object it is called on first where the
   operation takes it.
7. An object made: an exception is its constructor of `exn`, `Other "<class>"` for a class `exn` has none for; an
   anonymous class with no member, of a case of a sum, is that case; a class not read is `extern "<class>.apply"`.
   The arguments of an exception's constructor, and of a class not read, are not evaluated: an effect of the code
   read among them is refused (`Thread.currentThread()` is not one: it changes nothing and always returns).
8. Scala's library: `Option`, `Some`, `Left`, `Right`; a list's `::`, `head`, `tail`, `isEmpty`, `foreach`; a
   `Set[Thread]`'s `empty`, `contains`, `+`; `!`, `||`, `&&`; `asInstanceOf` (a cast). `==` is the equality of the
   type the values are read at: `Nat.eqb` (thread ids, handles), `Z.eqb`, `exn_eqb`; against an object of `obj`,
   `is_<name>`.
9. A closure applied: `invoke`.
10. A method of a class not read: a definition `C_m (this : nat) … := extern "<class>.<m>"`, written for the
    methods the unit calls, in the order the class declares them.

A call of anything else is refused.

### Coercions (`Coercions`)

| From | To | Is |
|---|---|---|
| an object of a class of the unit | `val` | `VObj (O_C x)` |
| `val` | a class of the unit | `cast_C`, a failed cast being `type_error` |
| `option val` | `option C` | `cast_option_C` |
| `val` | a list | `cast_list` (a list of `val`s) |
| a case of a sum | the sum | the case's constructor |
| a sum | one of its cases (`asInstanceOf`) | `cast_<case>` |
| a value | an option | `Some` |
| an option | what it holds | `unnull` |
| `Unit` | `val` | `VUnit` |

The casts a file holds are those its definitions mention, in the order of first mention, one that calls another
directly after it. A top-level value of a class not read, or a `ThreadLocal`, is a fixed handle (`Definition name :
nat := 0`, the next of the same class `1`): its initialiser is not read.

## The tables

| Table | Where | Holds |
|---|---|---|
| the unit | `ThreadUnit` (Ox's: `OxUnit`) | the classes read as types; the methods read, by group; the classes not read; the class of the capabilities a caller's closure holds |
| JDK method to operation | `Jdk.methods`, `Jdk.set`, `Jdk.traversal` | `AtomicBoolean.get` is `AbGet`, …; a concurrent set's by what it holds |
| JDK class to type | `Jdk.types`, `Jdk.ambient` | `Thread` is `tid`, the atomics, `CompletableFuture`, `ThreadLocal` and the sets are references |
| exception class to `exn` | `Thrown.classes` | the six constructors of `exn`, `ExecutionException` with `getCause` |
| names a variable cannot keep | `Reserved.words` | Rocq's keywords, the constants of `Lang.v` and `Jdk.v` |

The frame of the file is fixed text: the imports, `Client (n : nat) (caps : list <capability>)`, the two
abbreviations `val` and `M`, and the section `Interp` with its variable `client`.

## What is not read

- `ox.ErrorMode`, `ox.ForkLocalMap` and `ThreadFactory` (`OxUnit.opaque`): a value of one is a handle, a call
  `extern`.
- Whatever the rules refuse. A definition whose body holds a refused construct is `chaos "<its name>"`; a call of
  an inline method whose body holds one is `chaos "<the method>"`. In Ox's unit there is one: `chaos
  "ox.uninterruptible"` in `runFinalizers` (`List.flatMap`, and under it `UnsupervisedFork.joinEither`, are not
  read). The suite pins this list.

## What is trusted

- The rules above, and their implementation. `Agree.v` checks the result against `Code.v` for this unit only.
- `Jdk.v`: each contract, and what it does not model (integer overflow, a `Throwable`'s identity and message, null
  where a `val` is).
- The tables: that each method named has the operation given, and no other effect.
- That code not read touches nothing of the JDK's state read here (`extern`), and that arguments not evaluated
  (an exception's message, the arguments of a class not read) have no effect and end.
- That an exception is of a class of `Thrown.classes` exactly when it is that constructor: a caller's exception
  (`Thrown n`) is taken not to extend one of them.
- That `==` on a handle is the object's identity: a class not read is taken not to override `equals`.
- That a top-level value of a class not read, or a `ThreadLocal`, exists before the code runs.
- The TASTy reader of the Scala compiler, and that the jar's TASTy is the code its class files run.

## The agreement with `Code.v`

`Gen.v` is complete and stands alone. The suite checks that it is `Code.v` sentence for sentence once comments
and spacing are taken out, with the differences pinned (`OxUnit.reordered`).

`Agree.v` imports both. For each type it defines the function from `Gen`'s to `Code`'s and back, constructor by
constructor, which Rocq accepts only if the constructors take the same arguments. It then holds the text of
`Gen.v`'s definitions again in `Module Over`, where they are read over `Code.v`'s types (the suite checks the text
is the same), and proves each equal to `Code.v`'s definition of the same name by `reflexivity`.
