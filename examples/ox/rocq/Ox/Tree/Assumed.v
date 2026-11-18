(** What the kernel of Ox takes from the JDK, member by member, and where each is spoken of.

    `Kernel.kernel_jdk` is every definition of the JDK that the kernel of Ox reads or calls, computed from Ox's
    trees. Each is given its standing here:

    - `Stateful`: a call of it reads or changes what threads share (an atomic, a set, a thread, a future). The
      machine that runs Ox's trees runs for it what `FrFlow.Scala.Jdk` says (`Meant.kernel_unmeant`: no member
      of the JDK is among what has no meaning). The model of Ox's threads (`examples/ox`) reads five files of
      the kernel, and assumes of a member what the assumptions named here say, each set beside the JDK's
      documentation and code in `examples/ox/JDK.md`; a member with none named is called only by code of the
      kernel that the model does not read. The model's suite checks that each name is an assumption of the model.
    - `Data`: it makes or reads a value that no two threads share a state of: an exception made, a text, a test
      of a class.
    - `Trusted`: taken as said, with no meaning beside.

    `assumed_whole` says no member is left out: Rocq checks the table against the list computed from the trees.
    Kept by hand. *)

From Stdlib Require Import String List.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Program Ox.Tree.All Ox.Tree.Kernel.
Import ListNotations.
Open Scope string_scope.

Inductive standing :=
  | Stateful (assumed_by_the_model : list string)
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
   (Member "java.lang.Iterable" "forEach" "java.util.function.Consumer:scala.Unit", Stateful ["aTraversalAppliesItsFunctionToElements"; "aTraversalReachesWhatStays"; "aTraversalThrowsOnlyWhatItsFunctionThrew"; "aTraversalRespondsOnceItsFunctionDoes"]);
   (Member "java.lang.Object" "<init>" ":java.lang.Object", Data "an object made");
   (Member "java.lang.Object" "eq" "java.lang.Object:scala.Boolean", Data "the identity of two objects");
   (Member "java.lang.RuntimeException" "<init>" "java.lang.String:java.lang.RuntimeException", Data "an exception made: a value");
   (Member "java.lang.String" "+" "java.lang.Object:java.lang.String", Data "a text");
   (Member "java.lang.String" "hashCode" ":scala.Int", Data "a number of a text");
   (Member "java.lang.System$" "nanoTime" ":scala.Long", Stateful []);
   (Member "java.lang.Thread" "getName" ":java.lang.String", Data "a thread's name: a text");
   (Member "java.lang.Thread" "interrupt" ":scala.Unit", Stateful ["interruptReturns"; "interruptResponds"]);
   (Member "java.lang.Thread" "join" ":scala.Unit", Stateful ["joinThrowsOnlyAnInterruption"; "joinRespondsOnceItsThreadHasRun"]);
   (Member "java.lang.Thread" "start" ":scala.Unit", Stateful ["aThreadActsOnlyOnceStarted"; "aStartedThreadRunsItsFunction"]);
   (Member "java.lang.Thread$" "currentThread" ":java.lang.Thread", Stateful ["currentThreadIsTheCaller"; "currentThreadIsAnObject"; "currentThreadResponds"]);
   (Member "java.lang.Thread$" "interrupted" ":scala.Boolean", Stateful []);
   (Member "java.lang.Thread$" "ofVirtual" ":java.lang.Thread$.Builder$.OfVirtual", Trusted "the factory of virtual threads makes threads as a thread factory does");
   (Member "java.lang.Thread$" "sleep" "scala.Long:scala.Unit", Stateful []);
   (Member "java.lang.Thread$" "yield" ":scala.Unit", Stateful []);
   (Member "java.lang.Thread$.Builder" "factory" ":java.util.concurrent.ThreadFactory", Trusted "the factory of virtual threads makes threads as a thread factory does");
   (Member "java.lang.ThreadLocal" "<init>" "1:java.lang.ThreadLocal", Trusted "a thread local is made once, before the code read runs");
   (Member "java.lang.ThreadLocal" "get" ":java.lang.Object", Stateful ["theCurrentScopeIsReadAndSet"; "theCurrentScopeResponds"]);
   (Member "java.lang.ThreadLocal" "set" "java.lang.Object:scala.Unit", Stateful ["theCurrentScopeIsReadAndSet"; "theCurrentScopeResponds"]);
   (Member "java.lang.Throwable" "<init>" "java.lang.String:java.lang.Throwable", Data "an exception made: a value");
   (Member "java.lang.Throwable" "addSuppressed" "java.lang.Throwable:scala.Unit", Stateful ["addSuppressedReturns"; "addSuppressedResponds"]);
   (Member "java.lang.Throwable" "getCause" ":java.lang.Throwable", Data "the cause an ExecutionException holds");
   (Member "java.util.NoSuchElementException" "<init>" ":java.util.NoSuchElementException", Data "an exception made: a value");
   (Member "java.util.NoSuchElementException" "<init>" "java.lang.String:java.util.NoSuchElementException", Data "an exception made: a value");
   (Member "java.util.Set" "add" "java.lang.Object:scala.Boolean", Stateful ["addingIsAtomic"; "anElementEntersOnlyWhenAdded"; "anElementWasAdded"; "addingResponds"]);
   (Member "java.util.concurrent" "ConcurrentHashMap" "", Data "an object named: no call");
   (Member "java.util.concurrent.ArrayBlockingQueue" "<init>" "1,scala.Int:java.util.concurrent.ArrayBlockingQueue", Stateful []);
   (Member "java.util.concurrent.ArrayBlockingQueue" "put" "java.lang.Object:scala.Unit", Stateful []);
   (Member "java.util.concurrent.ArrayBlockingQueue" "take" ":java.lang.Object", Stateful []);
   (Member "java.util.concurrent.CompletableFuture" "<init>" "1:java.util.concurrent.CompletableFuture", Stateful []);
   (Member "java.util.concurrent.CompletableFuture" "complete" "java.lang.Object:scala.Boolean", Stateful []);
   (Member "java.util.concurrent.CompletableFuture" "completeExceptionally" "java.lang.Throwable:scala.Boolean", Stateful []);
   (Member "java.util.concurrent.CompletableFuture" "exceptionNow" ":java.lang.Throwable", Stateful []);
   (Member "java.util.concurrent.CompletableFuture" "get" ":java.lang.Object", Stateful []);
   (Member "java.util.concurrent.CompletableFuture" "isCompletedExceptionally" ":scala.Boolean", Stateful []);
   (Member "java.util.concurrent.ConcurrentHashMap$" "newKeySet" "1:java.util.concurrent.ConcurrentHashMap$.KeySetView", Stateful ["aKeySetHasOnlyItsMethods"; "makingASetReturnsInTime"]);
   (Member "java.util.concurrent.ConcurrentHashMap$.CollectionView" "isEmpty" ":scala.Boolean", Stateful ["isEmptyFindsItEmptyUnlessAdded"; "isEmptyFindsARestingSetEmpty"; "isEmptyReturns"; "isEmptyResponds"]);
   (Member "java.util.concurrent.ConcurrentHashMap$.KeySetView" "add" "java.lang.Object:scala.Boolean", Stateful ["addingIsAtomic"; "anElementEntersOnlyWhenAdded"; "anElementWasAdded"; "addingResponds"]);
   (Member "java.util.concurrent.ConcurrentHashMap$.KeySetView" "contains" "java.lang.Object:scala.Boolean", Stateful ["whatTheChecksAskOfTheJdkStaysOutOfHerds"]);
   (Member "java.util.concurrent.ConcurrentHashMap$.KeySetView" "forEach" "java.util.function.Consumer:scala.Unit", Stateful ["aTraversalAppliesItsFunctionToElements"; "aTraversalReachesWhatStays"; "aTraversalThrowsOnlyWhatItsFunctionThrew"; "aTraversalRespondsOnceItsFunctionDoes"]);
   (Member "java.util.concurrent.ConcurrentHashMap$.KeySetView" "remove" "java.lang.Object:scala.Boolean", Stateful ["removingTakesTheElementOut"; "anElementLeavesOnlyWhenRemoved"; "removingResponds"]);
   (Member "java.util.concurrent.Semaphore" "<init>" "scala.Int:java.util.concurrent.Semaphore", Stateful []);
   (Member "java.util.concurrent.Semaphore" "acquire" ":scala.Unit", Stateful []);
   (Member "java.util.concurrent.Semaphore" "release" ":scala.Unit", Stateful []);
   (Member "java.util.concurrent.ThreadFactory" "newThread" "java.lang.Runnable:java.lang.Thread", Stateful ["aThreadRunsOneForkFunctionOnce"; "aFactoryStaysOutOfHerds"]);
   (Member "java.util.concurrent.TimeoutException" "<init>" "java.lang.String:java.util.concurrent.TimeoutException", Data "an exception made: a value");
   (Member "java.util.concurrent.atomic.AtomicBoolean" "<init>" "scala.Boolean:java.util.concurrent.atomic.AtomicBoolean", Stateful ["anAtomicBooleanHasOnlyItsMethods"; "makingAFlagReturnsInTime"]);
   (Member "java.util.concurrent.atomic.AtomicBoolean" "get" ":scala.Boolean", Stateful ["getGivesTheFlag"]);
   (Member "java.util.concurrent.atomic.AtomicBoolean" "getAndSet" "scala.Boolean:scala.Boolean", Stateful []);
   (Member "java.util.concurrent.atomic.AtomicBoolean" "set" "scala.Boolean:scala.Unit", Stateful ["settingIsAtomic"; "setReturns"; "aFlagBecomesOnlyWhatIsSet"; "settingResponds"]);
   (Member "java.util.concurrent.atomic.AtomicInteger" "<init>" "scala.Int:java.util.concurrent.atomic.AtomicInteger", Stateful []);
   (Member "java.util.concurrent.atomic.AtomicInteger" "decrementAndGet" ":scala.Int", Stateful []);
   (Member "java.util.concurrent.atomic.AtomicInteger" "incrementAndGet" ":scala.Int", Stateful []);
   (Member "java.util.concurrent.atomic.AtomicReference" "<init>" "1,java.lang.Object:java.util.concurrent.atomic.AtomicReference", Stateful ["makingAReferenceReturnsInTime"]);
   (Member "java.util.concurrent.atomic.AtomicReference" "getAndSet" "java.lang.Object:java.lang.Object", Stateful []);
   (Member "java.util.concurrent.atomic.AtomicReference" "updateAndGet" "java.util.function.UnaryOperator:java.lang.Object", Stateful []);
   (Member "java.util.concurrent.locks" "LockSupport" "", Data "an object named: no call");
   (Member "java.util.concurrent.locks.LockSupport$" "park" ":scala.Unit", Stateful [])].

Lemma assumed_whole : same kernel_jdk (map fst assumed) = true.
Proof. vm_compute. reflexivity. Qed.

Definition is_stateful (s : standing) : bool := match s with Stateful _ => true | _ => false end.
Definition is_trusted (s : standing) : bool := match s with Trusted _ => true | _ => false end.

(** 68 members: 43 with a state threads share, 21 data, 4 trusted. *)
Lemma assumed_standing :
  (length assumed, length (filter is_stateful (map snd assumed)), length (filter is_trusted (map snd assumed)))
  = (68, 43, 4).
Proof. vm_compute. reflexivity. Qed.
