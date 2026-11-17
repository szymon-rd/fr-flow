# What is assumed of the JDK, against the JDK

The model assumes statements about the JDK's classes that Ox calls (`examples/ox/README.md`, *What is assumed*).
None is derived: each is decided by the developer. This file sets each beside what the JDK says, so that the
decision can be made on what the JDK says and not on what the statement sounds like.

What was read: the sources of OpenJDK 21 (`java.base`, 21.0.13), their documentation comments and, where the
documentation promises less than the statement, the code. The published pages were not reachable from where
this was written; the documentation comments are what they are generated from.

Three kinds of basis are told apart:

- **documented**: the JDK's documentation says it.
- **implementation**: the documentation does not say it, or says less; the code of OpenJDK 21 does it. Another
  JDK, or a later one, may not.
- **condition**: it holds only of some uses, which the statement does not name.

## What a moment is

The statements speak of moments, and of what a set holds at one. A call that the JDK documents as atomic is
assumed to take effect at one moment between its call and its response, and each such effect at a moment of its
own (`removingTakesTheElementOut`: at that moment the element leaves "and nothing else"). Several threads can
be inside the JDK at once, so between two events of the code there can be several such effects. This is no
contradiction: a moment is not an event of the code. An execution has moments at which no event of the code
happens (the model's events have one for it), and the history of a real run is one with as many of them as
the JDK's own steps need. A statement proven of every execution that meets the assumptions is then proven of
that one.

## The set: `ConcurrentHashMap.newKeySet()`

| Assumed | Basis |
|---|---|
| `addingIsAtomic`: a call of `add` that returns put the element in at one moment during it. | documented, with the reading above. `ConcurrentHashMap`: "Retrievals reflect the results of the most recently completed update operations holding upon their onset", and an update of a key "bears a happens-before relation with any (non-null) retrieval for that key reporting the updated value". In the code the node is linked under the bin's lock, or by one compare-and-set into an empty bin (`putVal`). `add(null)` throws; the statement is of calls that return. |
| `anElementLeavesOnlyWhenRemoved`, `anElementEntersOnlyWhenAdded`: what a set holds changes only during a call that removes, or adds, that element. | documented for a set on which only `add`, `remove`, `contains`, `isEmpty` and `forEach` are called, which is what the statements require (`plainSet`); the set made by `newKeySet()` is backed by a map of its own, which no call gives out. |
| `removingTakesTheElementOut`: a call of `remove` on an object that is not null takes it out at one moment during the call, and nothing else. | documented as for `add`. In the code the node is unlinked under the bin's lock (`replaceNode`). `remove(null)` throws; the statement leaves null out. |
| `anElementWasAdded`: what is in the set is there by a call of `add` that returns. | documented that it got there by `add`. That the call returns is beyond it: it is so if the thread that added is given its turn (`add` does not block, and does not throw on an object that is not null). The statement has a part about time in it. |
| `aTraversalAppliesItsFunctionToElements`: `forEach` applies its function only to what was in the set at a moment from its call to the application. | implementation, in line with what is documented of iterators: they "return elements reflecting the state of the hash table at some point at or since the creation of the iterator". `KeySetView.forEach` is no iterator; it walks the table with the same `Traverser` the iterators use. |
| `aTraversalReachesWhatStays`: a `forEach` that returns has applied its function to each element that was in the set from its call to its return. | implementation, in line with what `java.util.concurrent` documents of its iterators (weakly consistent: "they are guaranteed to traverse elements as they existed upon construction exactly once"). As above, `forEach` is the same walk; the walk follows a table being resized. |
| `aTraversalThrowsOnlyWhatItsFunctionThrew`: `forEach` with a function that is not null returns, or throws what a call of the function threw. | implementation: the code is a loop that calls the function; with `null` it throws, which the statement leaves out. Errors of the JVM (no memory, no stack) are not modelled anywhere. |
| `isEmptyReturns`: `isEmpty` does not throw. | implementation: a sum of counters compared with zero. |
| `isEmptyFindsItEmptyUnlessAdded`: an answer "empty", with no call adding during the call, means the set was empty at a moment during it. | **implementation only, against the documentation's advice.** The JDK says: the results of "aggregate status methods including size, isEmpty, and containsValue are typically useful only when a map is not undergoing concurrent updates in other threads. Otherwise the results of these methods reflect transient states that may be adequate for monitoring or estimation purposes, but not for program control." The statement is what `sumCount` gives: `add` and `remove` change the count after they have changed the table, so with every `add` over each increment is in the sum, each decrement in it is of an element already out, and a sum of zero or less means nothing is in the set when the call ends. |
| `isEmptyFindsARestingSetEmpty`: a set that holds nothing from a moment on answers "empty" to a call made once each `remove` made before that moment is over. | **implementation only**, as above. A `remove` made after the set emptied finds nothing and counts nothing; those made before are over, so every decrement is in the sum before the call reads it (the base count and each cell, which a later resize of the cells keeps); an increment not yet counted only lowers the sum. |

Ox uses `isEmpty` for program control (closing loops until it answers "empty"), which the JDK advises against.
That is where `nothingIsAddedDuringTheLastCheck`, false of Ox 1.1.0, comes from; and it is why the two
statements about `isEmpty` cannot be had from the documentation.

## The flag: `AtomicBoolean`

| Assumed | Basis |
|---|---|
| `getGivesTheFlag`, `settingIsAtomic`, `aFlagBecomesOnlyWhatIsSet`, `setReturns`: a read gives what the flag holds at a moment during it; `set` takes effect at one moment and returns; the flag changes only by `set`, where only `get` and `set` are called on it. | documented: `get` and `set` have the memory effects of a volatile read and write (`VarHandle.getVolatile`, `setVolatile`). |
| `anAtomicBooleanHasOnlyItsMethods`, `aKeySetHasOnlyItsMethods`: on what `new AtomicBoolean` or `newKeySet()` returned, only methods of that class are called. | documented: what the two return is of the class. |

## Threads

| Assumed | Basis |
|---|---|
| `currentThreadIsTheCaller`, `currentThreadIsAnObject`: `Thread.currentThread()` gives the calling thread, and no null. | documented: "Returns the Thread object for the current thread." In a virtual thread it is the virtual thread. |
| `aThreadDoesOneThingAtATime`. | the JVM: a thread executes one frame at a time. |
| `aCallEndsAfterTheCallsItMade`: a call is responded to only once each call it made itself is over. | the JVM: a method returns to the frame that invoked it, and a frame is the current one only once the frames above it are gone. |
| `joinThrowsOnlyAnInterruption`: `join` returns or throws an `InterruptedException`. | documented; `join()` is final, so it is `Thread`'s whatever the thread's class. |
| `interruptReturns`: `interrupt` returns. | **condition.** Documented to throw a `SecurityException` "if the current thread cannot modify this thread". That needs a security manager: none can be installed from JDK 24 on; in JDK 21, which Ox runs on, one can if the JVM is started to allow it. And `interrupt()` is not final: a thread of a class that overrides it does what that class says. It holds of threads of the JDK's own classes with no security manager. |
| `aThreadActsOnlyOnceStarted`: a thread a factory made makes no call before `start` is called on it. | documented, of a factory that keeps `ThreadFactory`'s contract: `newThread` "constructs a new unstarted Thread", and a thread begins to execute when `start` is called. The contract also lets `newThread` return null, of which the statement says nothing. |
| `theJdkStaysOutOfHerds`, `whatTheChecksAskOfTheJdkStaysOutOfHerds`: while a thread is in `get`, `add`, `start`, `currentThread`, `getName`, `contains` or reads its scope, it neither closes a herd nor removes from a herd's set. | **condition.** `add` and `contains` call the object's `hashCode` and `equals`, and `start()` is not final: for a thread of a class that overrides one of the three, what happens there is that class's code. It holds of threads of the JDK's own classes, such as those of the factory Ox uses unless given another. |
| `addSuppressedReturns`: `addSuppressed`, on an exception that is not null, given an `InterruptedException` the JDK threw, returns. | documented, with one remark. It throws if given the exception itself. In the JVM each `join` that throws makes a new exception, so the two are never one object; the model has one value for every `InterruptedException` the JDK throws, and the statement is read of the JVM's objects. |
| `theCurrentScopeIsReadAndSet`: `get` and `set` of the `ThreadLocal` return. | documented. |

## Fields: the JVM

What is assumed of who writes and who reads a field is of the JVM, not of the JDK's classes. The specifications
(JVMS, JLS) were not reachable from where this was written: the clauses are given by number and paraphrased, not
quoted. What could be read is Ox's bytecode (`javap -p -c` on the jar the model reads), and it is set beside
each.

| Assumed | Basis |
|---|---|
| `aHerdsValsAreAssignedWhereItIsMade`, `aScopesValsAreAssignedWhereItIsMade`: a val of a herd, or of a scope, is marked and written only by the thread that makes the object, inside the call that makes it. | the JVM, with a **condition**. A val is compiled to a `final` field: in the bytecode the four fields of `ThreadHerd` and the six of `OxError` are `private final`. `putfield` on a final field is let only in an instance initialisation method of the field's class (JVMS 6.5, putfield; otherwise `IllegalAccessError`), and such a method runs on an object once, where the object is created (JVMS 4.10.2.4). In the bytecode the only `putfield`s of these fields are in the two constructors, on `this`. The model has the constructor's events as events of the call that makes the object, where the code makes it in place. The condition: no reflection (`Field.setAccessible` lets a final instance field be set), no `Unsafe`, no native code. |
| `aHerdsValsAreReadByItsCode`: a val of a herd is read only by a method of the herd called on it, or by the function `startThread` handed its factory, after the call was made. | the JVM and the code, with the same **condition**. The fields are private: only code of the class (its nest) is let read them (JVMS 5.4.4). In the bytecode the `getfield`s of the four fields are in the six methods and in `$anonfun$1`, the function `startThread` hands the factory, each on `this`; the static methods closing's functions are compiled to read none. |
| `aScopesValsAreReadOnceItIsConstructed`: a val of a scope is read only once a call of the class's constructor has returned the scope. | the code, and who is given a scope. The constructor assigns the six fields and hands `this` to nothing (the lazy val of its trait is made on first use, after it); so no other thread has the scope before the constructor returns. It is the condition under which the JVM lets every reader of a final field see it assigned (JLS 17.5: the object is seen only after its constructor has finished). The fields are read through the scope's accessors, by any code that holds the scope: who holds one is not modelled, so this is assumed. |
| `herdsAreConstructed`: a method of a herd is called only on a herd that is ready (its constructor has returned it, or a scope that the call making a scope returned holds it). | the code: the herd's constructor hands `this` to nothing, and the scope's `apply` hands the herd it makes only to the scope it returns. |
| `closingKeepsItsVariableToItself`: what a call of closing itself makes, only the thread that called closing reads, marks and writes. | the code and the JDK, **implementation**. The two variables are `scala.runtime.ObjectRef`s, whose `elem` is a public field that is neither final nor volatile: nothing but who holds them keeps them from another thread. They are held by the two functions closing hands `forEach`, and `KeySetView.forEach` in OpenJDK 21 applies its function in the calling thread and keeps it nowhere. |

What a data race is here: two accesses to a field by two threads, one of them a write, not ordered by
happens-before (JLS 17.4.1, 17.4.5). The model writes a field in two events, and takes a read, a mark or a
write by another thread between them as the race. Over every order of the threads' turns the two agree: two
plain accesses by two threads that come next to each other have nothing between them to order them, and where
two can come next to each other, the second can come between the mark and the write of the first.

## In time

| Assumed | Basis |
|---|---|
| `currentThreadResponds`, `interruptResponds`, `addSuppressedResponds`, `settingResponds`, `isEmptyResponds`, `addingResponds`, `removingResponds`: the call is responded to. | implementation, given the caller its turn: none of them blocks. `add` and `remove` take a bin's lock, held by other threads for a bounded number of their own steps. |
| `theCurrentScopeResponds`: `get` and `set` of the `ThreadLocal` are responded to. | implementation, given the caller its turn: neither blocks. |
| `makingAFlagReturnsInTime`, `makingASetReturnsInTime`, `makingAReferenceReturnsInTime`: `new AtomicBoolean`, `ConcurrentHashMap.newKeySet()` and `new AtomicReference` return, in time. | documented that each makes the object; implementation that none blocks. Errors of the JVM (no memory) are not modelled. |
| `aTraversalRespondsOnceItsFunctionDoes`: `forEach` on a set to which nothing more is added is responded to, if each call of its function is. | implementation: the walk is over a table that no longer grows. |
| `joinRespondsOnceItsThreadHasRun`: `join` on a thread a factory made for a function is responded to, once the thread's call of the function has been. | documented ("Waits for this thread to terminate"), of a thread whose `run` is the function it was made for: it terminates when the function ends. |
| `aStartedThreadRunsItsFunction`: a thread a factory made for a function calls it, once started. | documented (`start`: "Schedules this thread to begin execution"), of such a thread, and of a scheduler that gives it a turn. |

## What the review found

1. **An interruption before a thread is started.** `forkCodeCompletesOnceInterrupted` asks the code of a fork to
   end once its thread has been interrupted, whenever that was, and closing can interrupt a thread that
   `startThread` has added and not yet started. Of that the JDK says: "Interrupting a thread that is not alive
   need not have any effect", and, as a note on its own implementation, that it "still records that the
   interrupt request was made". So on OpenJDK the request is kept, and code that ends when it finds its thread
   interrupted meets the assumption; by the documentation alone the request may be lost. Ox itself needs it
   kept: closing interrupts the threads in the set and then joins them, and a thread started between the two,
   whose interruption was lost, is joined while it runs uninterrupted. (A thread not yet started when it is
   joined is no problem: joining it returns at once, and the next turn of closing's loop interrupts it again.)
   The assumption is therefore of the user's code and of the JVM together: it holds of code that ends on
   interruption, on a JVM that keeps an interruption made before the start, as OpenJDK does.
2. **`isEmpty`** is assumed as OpenJDK implements it, not as documented (above).
3. **Threads of other classes.** `interrupt()` and `start()` are not final, and a set calls `hashCode` and
   `equals`: what is assumed of them is of `java.lang.Thread`'s own. A thread factory that returns threads of a
   class overriding them is outside what is assumed. This is a restriction on the factory a herd is given,
   beside the two the model names (`aThreadRunsOneForkFunctionOnce`, `aFactoryStaysOutOfHerds`); it is not yet
   a statement of its own.
4. **A security manager** makes `interruptReturns` false; from JDK 24 there is none.
5. **A factory that returns null**: `startThread` then throws from `add`; nothing assumed is false of it, and
   nothing is claimed of it.
6. **Errors of the JVM** (`OutOfMemoryError`, `StackOverflowError`) are not modelled: "returns" is said of calls
   that the JVM lets run.
7. **Reflection, `Unsafe` and native code** can write a final field and read a private one: what is assumed of
   fields is of a program that does neither to Ox's objects.
8. **The scope's constructor as read.** The model first assumed that a herd is one a call of its constructor
   returned. That is false of the herds Ox's own code makes: the scope's `apply`, read from the jar, makes its
   herd in place, and in the model that is no call of the constructor. The statement now says a herd is ready
   when either has happened, and what was proven of a constructed herd is proven of a ready one.
