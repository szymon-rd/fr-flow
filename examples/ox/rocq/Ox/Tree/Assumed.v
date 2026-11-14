(** What Ox's concurrency assumes of the JDK, member by member.

    `Kernel.kernel_jdk` is every definition of the JDK that the kernel of Ox reads or calls, computed from Ox's
    trees. Each is given its standing here:

    - `Contract`: what a call of it may do is said by an operation of `FrFlow.Threads.Jdk` (its state, its
      result, when it returns), taken as an assumption. The proofs about Ox rest on these and on nothing else of
      the JDK's behaviour.
    - `Data`: it makes or reads a value that no two threads share a state of: an exception made, a text, a test
      of a class.
    - `Trusted`: taken as said, with no contract.

    `assumed_whole` says no member is left out: Rocq checks the table against the list computed from the trees.
    Kept by hand. *)

From Stdlib Require Import String List.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Program Ox.Tree.All Ox.Tree.Kernel.
Import ListNotations.
Open Scope string_scope.

Inductive standing :=
  | Contract (operations : string)
  | Data (what : string)
  | Trusted (what : string).

Definition assumed : list (sym * standing) :=
  [(Member "java.lang" "System" "", Data "an object named: no call");
   (Member "java.lang" "Thread" "", Data "an object named: no call");
   (Member "java.lang.AutoCloseable" "close" ":scala.Unit", Trusted "a resource's close is the client's code: it is asked of the client");
   (Member "java.lang.Class" "isInstance" "java.lang.Object:scala.Boolean", Data "a test of a value's class");
   (Member "java.lang.IllegalStateException" "<init>" ":java.lang.IllegalStateException", Data "an exception made: a value");
   (Member "java.lang.IllegalStateException" "<init>" "java.lang.String:java.lang.IllegalStateException", Data "an exception made: a value");
   (Member "java.lang.IndexOutOfBoundsException" "<init>" "scala.Int:java.lang.IndexOutOfBoundsException", Data "an exception made: a value");
   (Member "java.lang.InterruptedException" "<init>" ":java.lang.InterruptedException", Data "an exception made: a value");
   (Member "java.lang.InterruptedException" "<init>" "java.lang.String:java.lang.InterruptedException", Data "an exception made: a value");
   (Member "java.lang.Iterable" "forEach" "java.util.function.Consumer:scala.Unit", Contract "EsNext, VsNext");
   (Member "java.lang.Object" "<init>" ":java.lang.Object", Data "an object made");
   (Member "java.lang.Object" "eq" "java.lang.Object:scala.Boolean", Data "the identity of two objects");
   (Member "java.lang.RuntimeException" "<init>" "java.lang.String:java.lang.RuntimeException", Data "an exception made: a value");
   (Member "java.lang.String" "+" "java.lang.Object:java.lang.String", Data "a text");
   (Member "java.lang.String" "hashCode" ":scala.Int", Data "a number of a text");
   (Member "java.lang.System$" "nanoTime" ":scala.Long", Contract "NanoTime");
   (Member "java.lang.Thread" "getName" ":java.lang.String", Data "a thread's name: a text");
   (Member "java.lang.Thread" "interrupt" ":scala.Unit", Contract "ThreadInterrupt");
   (Member "java.lang.Thread" "join" ":scala.Unit", Contract "ThreadJoin");
   (Member "java.lang.Thread" "start" ":scala.Unit", Contract "ThreadStart");
   (Member "java.lang.Thread$" "currentThread" ":java.lang.Thread", Contract "CurrentThread");
   (Member "java.lang.Thread$" "interrupted" ":scala.Boolean", Contract "ThreadInterrupted");
   (Member "java.lang.Thread$" "ofVirtual" ":java.lang.Thread$.Builder$.OfVirtual", Trusted "the factory of virtual threads makes threads as NewThread says");
   (Member "java.lang.Thread$" "sleep" "scala.Long:scala.Unit", Contract "ThreadSleep");
   (Member "java.lang.Thread$" "yield" ":scala.Unit", Contract "ThreadYield");
   (Member "java.lang.Thread$.Builder" "factory" ":java.util.concurrent.ThreadFactory", Trusted "the factory of virtual threads makes threads as NewThread says");
   (Member "java.lang.ThreadLocal" "<init>" "1:java.lang.ThreadLocal", Trusted "a thread local is made once, before the code read runs");
   (Member "java.lang.ThreadLocal" "get" ":java.lang.Object", Contract "TlGet");
   (Member "java.lang.ThreadLocal" "set" "java.lang.Object:scala.Unit", Contract "TlSet");
   (Member "java.lang.Throwable" "<init>" "java.lang.String:java.lang.Throwable", Data "an exception made: a value");
   (Member "java.lang.Throwable" "addSuppressed" "java.lang.Throwable:scala.Unit", Contract "AddSuppressed");
   (Member "java.lang.Throwable" "getCause" ":java.lang.Throwable", Data "the cause an ExecutionException holds");
   (Member "java.util.NoSuchElementException" "<init>" ":java.util.NoSuchElementException", Data "an exception made: a value");
   (Member "java.util.NoSuchElementException" "<init>" "java.lang.String:java.util.NoSuchElementException", Data "an exception made: a value");
   (Member "java.util.Set" "add" "java.lang.Object:scala.Boolean", Contract "EsAdd, VsAdd");
   (Member "java.util.concurrent" "ConcurrentHashMap" "", Data "an object named: no call");
   (Member "java.util.concurrent.ArrayBlockingQueue" "<init>" "1,scala.Int:java.util.concurrent.ArrayBlockingQueue", Contract "BqNew");
   (Member "java.util.concurrent.ArrayBlockingQueue" "put" "java.lang.Object:scala.Unit", Contract "BqPut");
   (Member "java.util.concurrent.ArrayBlockingQueue" "take" ":java.lang.Object", Contract "BqTake");
   (Member "java.util.concurrent.CompletableFuture" "<init>" "1:java.util.concurrent.CompletableFuture", Contract "CfNew");
   (Member "java.util.concurrent.CompletableFuture" "complete" "java.lang.Object:scala.Boolean", Contract "CfComplete");
   (Member "java.util.concurrent.CompletableFuture" "completeExceptionally" "java.lang.Throwable:scala.Boolean", Contract "CfCompleteExceptionally");
   (Member "java.util.concurrent.CompletableFuture" "exceptionNow" ":java.lang.Throwable", Contract "CfExceptionNow");
   (Member "java.util.concurrent.CompletableFuture" "get" ":java.lang.Object", Contract "CfGet");
   (Member "java.util.concurrent.CompletableFuture" "isCompletedExceptionally" ":scala.Boolean", Contract "CfIsCompletedExceptionally");
   (Member "java.util.concurrent.ConcurrentHashMap$" "newKeySet" "1:java.util.concurrent.ConcurrentHashMap$.KeySetView", Contract "TsNew, EsNew, VsNew");
   (Member "java.util.concurrent.ConcurrentHashMap$.CollectionView" "isEmpty" ":scala.Boolean", Contract "TsIsEmpty");
   (Member "java.util.concurrent.ConcurrentHashMap$.KeySetView" "add" "java.lang.Object:scala.Boolean", Contract "TsAdd");
   (Member "java.util.concurrent.ConcurrentHashMap$.KeySetView" "contains" "java.lang.Object:scala.Boolean", Contract "TsContains");
   (Member "java.util.concurrent.ConcurrentHashMap$.KeySetView" "forEach" "java.util.function.Consumer:scala.Unit", Contract "TsNext");
   (Member "java.util.concurrent.ConcurrentHashMap$.KeySetView" "remove" "java.lang.Object:scala.Boolean", Contract "TsRemove");
   (Member "java.util.concurrent.Semaphore" "<init>" "scala.Int:java.util.concurrent.Semaphore", Contract "SemNew");
   (Member "java.util.concurrent.Semaphore" "acquire" ":scala.Unit", Contract "SemAcquire");
   (Member "java.util.concurrent.Semaphore" "release" ":scala.Unit", Contract "SemRelease");
   (Member "java.util.concurrent.ThreadFactory" "newThread" "java.lang.Runnable:java.lang.Thread", Contract "NewThread");
   (Member "java.util.concurrent.TimeoutException" "<init>" "java.lang.String:java.util.concurrent.TimeoutException", Data "an exception made: a value");
   (Member "java.util.concurrent.atomic.AtomicBoolean" "<init>" "scala.Boolean:java.util.concurrent.atomic.AtomicBoolean", Contract "AbNew");
   (Member "java.util.concurrent.atomic.AtomicBoolean" "get" ":scala.Boolean", Contract "AbGet");
   (Member "java.util.concurrent.atomic.AtomicBoolean" "getAndSet" "scala.Boolean:scala.Boolean", Contract "AbGetAndSet");
   (Member "java.util.concurrent.atomic.AtomicBoolean" "set" "scala.Boolean:scala.Unit", Contract "AbSet");
   (Member "java.util.concurrent.atomic.AtomicInteger" "<init>" "scala.Int:java.util.concurrent.atomic.AtomicInteger", Contract "AiNew");
   (Member "java.util.concurrent.atomic.AtomicInteger" "decrementAndGet" ":scala.Int", Contract "AiDecrementAndGet");
   (Member "java.util.concurrent.atomic.AtomicInteger" "incrementAndGet" ":scala.Int", Contract "AiIncrementAndGet");
   (Member "java.util.concurrent.atomic.AtomicReference" "<init>" "1,java.lang.Object:java.util.concurrent.atomic.AtomicReference", Contract "ArNew");
   (Member "java.util.concurrent.atomic.AtomicReference" "getAndSet" "java.lang.Object:java.lang.Object", Contract "ArGetAndSet");
   (Member "java.util.concurrent.atomic.AtomicReference" "updateAndGet" "java.util.function.UnaryOperator:java.lang.Object", Contract "ArUpdateAndGet");
   (Member "java.util.concurrent.locks" "LockSupport" "", Data "an object named: no call");
   (Member "java.util.concurrent.locks.LockSupport$" "park" ":scala.Unit", Contract "Park")].

Lemma assumed_whole : same kernel_jdk (map fst assumed) = true.
Proof. vm_compute. reflexivity. Qed.

Definition is_contract (s : standing) : bool := match s with Contract _ => true | _ => false end.
Definition is_trusted (s : standing) : bool := match s with Trusted _ => true | _ => false end.

(** 68 members: 43 under a contract, 21 data, 4 trusted. *)
Lemma assumed_standing :
  (length assumed, length (filter is_contract (map snd assumed)), length (filter is_trusted (map snd assumed)))
  = (68, 43, 4).
Proof. vm_compute. reflexivity. Qed.
