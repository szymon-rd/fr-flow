# Ox's threads: what is proven of a scope, and of `ThreadHerd`

A FrFlow model of `unsupervised` and `supervised`, of the scope class (`ox.OxError`), and of the class Ox keeps a
scope's threads in, `ox.internal.ThreadHerd`. The code is read from Ox's jar as it is compiled (its TASTy),
unchanged. The statements are Scala (`src/main/scala/ox/scopes`, `src/main/scala/ox/threads`); each step is
proven in Rocq (`rocq/Proofs/OxThreads`), the claims at the bottom against the trees read.

## What is stated

The roots, of a scope: after a call of `unsupervised` has completed, and the same after a call of `supervised`
(`supervisedError`, which `supervised` runs), of the herd of the scope the call made:

| Root | Says |
|---|---|
| `noForkRunsOnceUnsupervisedEnds`, `noForkRunsOnceSupervisedEnds` | No fork of the herd runs the code it was made to run. |
| `nothingIsAddedOnceUnsupervisedEnds`, `nothingIsAddedOnceSupervisedEnds` | No thread is added to the herd's set. |
| `noThreadIsStartedOnceUnsupervisedEnds`, `noThreadIsStartedOnceSupervisedEnds` | A call of `startThread` does not return, and adds no thread. |

Each is from what holds of a herd after `interruptAllAndJoinUntilCompleted` (closing) has completed, by its
owner:

| Statement | Says |
|---|---|
| `noForkRunsOnceClosed` | No fork of the herd runs the code it was made to run. |
| `nothingIsAddedOnceClosed` | No thread is added to the herd's set. |
| `aClosedHerdRefusesToStart` | A call of `startThread` does not return, and adds no thread. |

## What stands, and on what

All six roots are proven: every claim below each is proven, down to the trees of `unsupervised`, of
`supervised`, of the scope class and of `ThreadHerd`. No claim of the model is unproven; FrFlow reports it so,
and the suite pins it (`ThreadsSuite`).

Of a scope, four claims are proven of the trees. A call of `unsupervised` that made a scope completes only after
a call it made itself, running code in that scope, has completed (`unsupervisedRunsInTheScopeItMade`), and so
does a call of `supervised` (`supervisedRunsInTheScopeItMade`: it makes a supervisor and the scope, runs code
in the scope, and whatever that gives or throws, what it does next makes no other scope). Running code in a
scope completes only after closing the scope's herd has (`aScopeEndsAfterItsHerdIsClosed`: the function
`scopedWithCapability` applies closes the herd whatever the code gave). The herd a scope holds is one whose
owner is the thread that made the scope (`aScopesHerdIsItsMakers`: the herd's constructor, run where the scope
is made, writes the current thread as its owner). So the scope's herd is closed once the call has completed
(`unsupervisedClosesItsScopesHerd`, `supervisedClosesItsScopesHerd`).

What a statement is proven from is the assumptions below it, and they differ in kind, so it is worth what the
weakest of its assumptions is:

- That no thread is started (`noThreadIsStartedOnce…Ends`, `aClosedHerdRefusesToStart`) rests on the JDK, the
  JVM and Scala's objects, and on one assumption about Ox, `aHerdKeepsItsFlagToItself`, and no more. The suite
  pins it.
- That no fork runs and that nothing is added (`noForkRunsOnce…`, `nothingIsAddedOnce…`) rest, beside the
  platform, on every other kind below, and among them on `nothingIsAddedDuringTheLastCheck`, **which is
  suspected false**. They are proven from it; they are not known to hold of Ox.

Twenty-seven claims are proven of the code's trees, each gone through whole (the four of a scope among them).
Three are of what making a herd runs: a herd has been made, and its flag and its set are what
`new AtomicBoolean(false)` and `ConcurrentHashMap.newKeySet()` returned to the call that made it. Eight say what a piece of the herd's code
calls itself: one per method (`startThreadCallsFive`, `closingCallsFour`, `theClosingCheckCallsGet`,
`theTreeCheckCallsFour`, `theOwnerCheckCallsCurrentThread`, `theMembershipCheckCallsContains`), one for the
function `startThread` hands the factory (`theForkFunctionCallsFour`), and one for the function the tree check
applies to go up the scopes, which applies itself (`theWalkUpCallsFour`).

Thirty-three claims are proven of Ox's code from the JDK, the JVM and Scala's objects alone, with no assumption
about Ox or about who uses it (the suite computes the list and pins it). Among them:

- `startThreadFirstSeesTheFlagUnset`: a call of `startThread` returns, or adds a thread, only if the herd's
  flag was unset at a moment during the call.
- `closingSetsTheFlagItself`: closing, by the herd's owner, completes only after it has set the flag.
- `closingSetsTheFlagOnlyToTrue`: closing sets the flag to nothing but true.
- `aHerdsMethodsOnlyGetAndSetAFlag`: of the methods of an atomic boolean, a method of a herd itself calls only
  `get`, and closing `set(true)`.
- `whatAHerdsCodeCallsOfASet`: of the methods of a key set, `startThread` itself calls only `add`, closing
  `isEmpty` and `forEach`, the membership check `contains`, and the function `startThread` hands the factory
  `remove`.
- `theForkFunctionRemovesTheCurrentThread`: the function `startThread` hands the factory removes from the set
  only the thread `Thread.currentThread()` gave it.
- `aForkFunctionRemovesAfterTheCode`: that function removes only after its call of the code has completed.
- `theClosingCheckStaysOutOfHerds`, `theMembershipCheckStaysOutOfHerds`: a thread in `assertNotShuttingDown`
  or in `isOwnerOrHerdThread` neither closes a herd nor removes from a herd's set.

That closing's traversals do not throw is proven (`closingsTraversalsReturn`, `closingsFunctionsReturn`). The
function closing hands its second traversal, catching an interruption, reads closing's variable, finds it holds
an exception, and reads it again to add to it: the second read finds what the first did, by what is taken of a
variable (below), with nothing written between the two, the thread doing one thing at a time.

That a thread calling `startThread` neither closes a herd nor leaves one is proven
(`startThreadStaysOutOfHerds`), through the tree check: the function it applies goes up the scopes, applying
itself, and what holds of one application holds of the next by induction on when it was made
(`theWalkUpStaysOutOfHerds`).

What is assumed, by what it is about:

- **The JDK and the JVM** (19): `addingIsAtomic`, `anElementLeavesOnlyWhenRemoved`,
  `isEmptyFindsItEmptyUnlessAdded`, `isEmptyReturns`, `getGivesTheFlag`, `settingIsAtomic`,
  `aFlagBecomesOnlyWhatIsSet`, `setReturns`, `currentThreadIsTheCaller`, `theJdkStaysOutOfHerds`,
  `whatTheChecksAskOfTheJdkStaysOutOfHerds`, `aThreadDoesOneThingAtATime`,
  `aTraversalThrowsOnlyWhatItsFunctionThrew`, `joinThrowsOnlyAnInterruption`, `interruptReturns`,
  `addSuppressedReturns`, `anAtomicBooleanHasOnlyItsMethods`, `aKeySetHasOnlyItsMethods`,
  `theCurrentScopeIsReadAndSet`.
- **Scala's objects** (5): `herdsAreConstructed`, `aHerdKeepsItsFields`, `aHerdHoldsWhatItWasGiven`,
  `aScopeHoldsTheHerdItIsMadeWith` (the `apply` the compiler writes for a case class is in no tree read: a scope
  made with a herd holds that herd), `aScopeGivesTheHerdItHolds` (a scope's herd is a val, asked for through
  the trait that declares it).
- **Who uses a herd** (1): `startThreadIsCalledFromInside`. It is stricter than Ox's own check: it leaves out a
  fork of a nested scope starting a fork in an enclosing one.
- **The thread factory a herd is given** (2): `aThreadRunsOneForkFunctionOnce`, `aFactoryStaysOutOfHerds`.
- **That a private field stays private** (2): `aHerdKeepsItsFlagToItself`, `aHerdKeepsItsSetToItself`. What a
  herd holds as its flag is called on only by the herd's own methods, themselves; what it holds as its set, only
  by those and by the functions `startThread` handed its factory. Each is a private val, made in the constructor
  and handed to nothing; that then nothing else reaches it is what the JVM and Scala make of a private field
  without reflection. It is assumed, of these two fields, and not derived from the code. What is derived from
  it and the trees, and was assumed before: that only `get` and `set` are called on the flag
  (`aHerdsFlagIsOnlyReadAndSet`), that only closing sets it (`onlyClosingSetsTheFlag`), that only `add`,
  `remove`, `contains`, `isEmpty` and `forEach` are called on the set (`aHerdsSetIsPlain`), that only
  `startThread` adds to it (`onlyStartThreadAddsToTheSet`) and only a fork function removes from it
  (`onlyAForkFunctionRemoves`).
- **That a variable stays its call's** (1): `closingKeepsItsVariableToItself`. What a call of closing itself
  makes (the variable it keeps what interrupted it in), only the thread that called closing reads and writes.
  The functions closing hands its traversals hold the variable; the JDK's traversal applies them on the thread
  that called it and hands them to nothing. It is assumed, and not derived from the code.
- **Who reaches a thread and the code startThread is given** (2): `onlyItsMakerStartsAThread`,
  `onlyAForkFunctionCallsTheCode`. These are statements about Ox, of a local value and of a parameter, not yet
  derived from its code.
- **Ox's scopes, which are not read** (1): `aScopesHerdAndParentStayOutOfHerds`. Asking a scope for its herd or
  its parent neither closes a herd nor removes from a herd's set. Both are vals of a scope; the classes of
  scopes are not read here, so this is an assumption about code of Ox, the one of its kind.
- **Ox itself, suspected false** (1): `nothingIsAddedDuringTheLastCheck`. `isEmpty` on a concurrent set is no
  snapshot; a fork that starts another and leaves while closing asks can make it answer yes of a set that was
  never empty. That no fork runs and that nothing is added rest on it; that no thread is started does not.

A call of an inline method (`discard`, in the function `startThread` hands the factory) is, in the tree read
from TASTy, a call: the model has it as a call of a method outside the code, where the JVM runs its expansion
in place.

Beside the nodes, four things are taken of Scala and the JVM: what an execution of the code is (the meaning of
its trees in Rocq, written by hand and tested against the JVM, `docs/EXECUTIONS.md`); that the events of
threads come one after another; that what a thread reads of a variable is what was last written there, where
that thread alone made the variable and writes it (the order of one thread's own actions, JLS 17.4.5; nothing
is taken of a variable two threads write, nor of a field); and that the VM raises no error of its own. A value
of a class the trees give no meaning has the type its method's signature says: an option is none, some value,
or no object. What a method of the code gives is of the class its signature names too, and what a call throws
is an object like any other. A handler for every `Throwable` takes whatever is thrown, without looking at it.

## What is not covered

- `fork`, the supervisor and the scope's finalizers: they are not read. The roots say what holds of the herd of
  the scope a call made, once the call has completed; `startThread` is the herd's, which `fork` calls. Nothing
  is said of what `supervised` returns.
- That anything completes: closing, a scope, `supervised`.
- What is built on scopes (`par`, `race`, `timeout`, cancellation, error modes, `ForkLocal`), channels, `Flow`,
  retries and scheduling, actors.
- Every witness that the statements can hold together is the execution in which nothing happens.

## Checking it

```bash
sbt "oxModel/Rocq/testOnly ox.threads.ThreadsSuite"
```
