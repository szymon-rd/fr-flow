(** The memory model: why Ox's kernel may be read as threads taking steps in turn.

    Every proof here takes a run to be an interleaving of the threads' steps, each a call of a JDK operation at
    one moment. The Java Language Specification grants that reading to a program with no data race (17.4.5: "If
    a program is correctly synchronized, then all executions of the program will appear to be sequentially
    consistent"). A data race needs a variable two threads reach, one of them writing, with no synchronisation
    between. So the assumption has two halves:

    - of the JDK: its atomics, futures, concurrent sets, semaphores, queues and thread locals synchronise their
      own state, and `Thread.start` and `Thread.join` order what comes before and after them (their
      documentation, and the "Memory Consistency Properties" of `java.util.concurrent`). Taken with the
      contracts of `FrFlow.Threads.Jdk`.
    - of Ox: its own code shares no variable between threads. This half is checked below, on Ox's trees.

    `kernel_variables` is every variable the classes of the kernel declare: nine, of the 126 in all of Ox. Each
    is one of:

    - `Unshared`: a variable of one call of a method, which no function made inside the method reads or assigns
      (`captured`): only the thread making the call reaches it.
    - `CallersThread`: captured, by a function the calling thread itself runs before the method goes on: a
      concurrent set's `forEach` runs its function on its caller (`TsNext`, `EsNext`, `VsNext` are the caller's
      steps).
    - `SetOnce`: a field. Trusted: it is assigned before any scope is opened.

    Rocq checks that the list is exact and which of them are captured. Every other field of the kernel's classes
    is a `val`. Kept by hand. *)

From Stdlib Require Import String List.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Program Ox.Tree.All Ox.Tree.Kernel.
Import ListNotations.
Open Scope string_scope.

Inductive reach :=
  | Unshared
  | CallersThread (run_by : string)
  | SetOnce (before : string).

Definition kernel_variables : list (string * sym * reach) :=
  [("ox.DefaultSupervisor", Local "result" 10,
      CallersThread "addSuppressedErrors: the functions given to otherExceptions.forEach and otherErrors.forEach");
   ("ox.control$package$", Local "loop" 2, Unshared);
   ("ox.control$package$", Local "loop" 4, Unshared);
   ("ox.internal.ThreadHerd", Local "interruptedThreads" 4,
      CallersThread "interruptAllAndJoinUntilCompleted: interruptIfNeeded, given to threads.forEach");
   ("ox.internal.ThreadHerd", Local "interruptedException" 7,
      CallersThread "interruptAllAndJoinUntilCompleted: the function given to threads.forEach that joins each thread");
   ("ox.oxThreadFactory$package$", Member "ox.oxThreadFactory$package$" "customThreadFactory" "",
      SetOnce "setOxThreadFactory is called, if at all, before the first scope is opened");
   ("ox.resource$package$", Local "caught" 45, Unshared);
   ("ox.util$package$", Local "interrupted" 21, Unshared);
   ("ox.util$package$", Local "result" 22, Unshared)].

(** The variables of a class, each with the class. *)
Definition in_class {A : Type} (f : tree -> list A) : list (string * A) :=
  flat_map (fun c => if existsb (String.eqb (fst c)) (owners kernel) then map (pair (fst c)) (f (snd c)) else [])
    (classes files).

Lemma kernel_variables_whole :
  in_class (fun c => map fst (variables c)) = map fst kernel_variables.
Proof. vm_compute. reflexivity. Qed.

(** Those a function made inside their method reads or assigns: the three said to be run by the caller. *)
Lemma kernel_captured :
  in_class captured =
  [("ox.DefaultSupervisor", Local "result" 10); ("ox.internal.ThreadHerd", Local "interruptedThreads" 4);
   ("ox.internal.ThreadHerd", Local "interruptedException" 7)].
Proof. vm_compute. reflexivity. Qed.

(** All of Ox declares 126 variables; the kernel's classes, these nine. *)
Lemma variables_count : (length (flat_map variables files), length kernel_variables) = (126, 9).
Proof. vm_compute. reflexivity. Qed.
