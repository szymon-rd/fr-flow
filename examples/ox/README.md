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
| `whatAForkBeganIsOverOnceUnsupervisedEnds`, `whatAForkBeganIsOverOnceSupervisedEnds` | Each call that a fork of the herd began while running the code it was made to run is over. |
| `forkUnsupervisedIsRefusedOnceUnsupervisedEnds`, `forkUnsupervisedIsRefusedOnceSupervisedEnds` | A call of `forkUnsupervised` in the scope does not return. |
| `forkCancellableIsRefusedOnceUnsupervisedEnds`, `forkCancellableIsRefusedOnceSupervisedEnds` | A call of `forkCancellable` in the scope does not return. |
| `forkIsRefusedOnceSupervisedEnds`, `forkUserIsRefusedOnceSupervisedEnds` | A call of `fork`, or of `forkUser`, in the scope `supervised` made does not return. |

The last is the nesting of scopes: a scope a fork opened, by `unsupervised` or by `supervised`, is a call the
fork began while running its code, so it has ended by the time the scope the fork is of has.

That a fork is refused is what a user of Ox sees of the third: `forkUnsupervised`, read from Ox's code, returns
only after a call of `startThread` on the herd of its scope, that it made itself, has returned
(`forkUnsupervisedStartsAThread`, proven of its tree), and that call does not return once the herd is closed.
`forkCancellable` is the same (`forkCancellableStartsAThread`).

`fork` goes a longer way, and each step is proven of a tree. `fork` asks the scope for itself without an error
mode and calls `forkError` in what that gives (`forkStartsAThread`); `asNoErrorMode` gives the scope itself, or
a scope made of the scope's vals, which holds the same herd (`asNoErrorModeKeepsTheHerd`); `forkError` reads
the herd of its scope and calls `startThread` on it (`forkErrorStartsAThread`). A scope's vals and methods are
read from Ox's class `OxError`, so each of these is said of a scope that is an object of that class: the scope
`supervised` made is one (`aScopeMadeIsAnObject`), since the `apply` the compiler writes for a case class makes
the object by the class's constructor (assumed), and the constructor makes an object of the class
(`aConstructedScopeIsMade`). `forkUser` is `fork` with `forkUserError` for `forkError`, which first tells the
scope's supervisor that a fork starts (`forkUserStartsAThread`, `forkUserErrorStartsAThread`).

Each is from what holds of a herd after `interruptAllAndJoinUntilCompleted` (closing) has completed, by its
owner:

| Statement | Says |
|---|---|
| `noForkRunsOnceClosed` | No fork of the herd runs the code it was made to run. |
| `nothingIsAddedOnceClosed` | No thread is added to the herd's set. |
| `aClosedHerdRefusesToStart` | A call of `startThread` does not return, and adds no thread. |
| `whatAForkBeganIsOverOnceClosed` | Each call that a fork of the herd began while running the code it was made to run is over. |

That one is from `noForkRunsOnceClosed` and from how a thread's calls nest (`callsNest`: a call that a thread
begins while a call of its own is pending is over before that call is). The fork's call of its code was pending
when the call was begun, and is pending no more once the herd is closed. That calls nest is proven from two
statements about the JVM: a thread does one thing at a time, and a call is responded to only once each call it
made itself is over (`aCallEndsAfterTheCallsItMade`); by how far the inner call is from the outer one.

One statement says what happens in time:

| Root | Says |
|---|---|
| `aScopesHerdIsClosedInTime` | A call running code in a scope, by the thread that made the scope, closes the scope's herd in time, if each call of the code on the scope that the thread makes is responded to: closing is called, and is responded to. |

Running code in a scope is `scopedWithCapability`, which `unsupervised` and `supervised` both call, on the
thread that made the scope. The root is from three statements, each proven:

| Statement | Says |
|---|---|
| `aScopesClosingIsReached` | A call running code in a scope calls closing on the scope's herd in time, if each call of the code on the scope that its thread makes is responded to. |
| `aScopesHerdIsItsMakers` | The herd a scope holds is one whose owner is the thread that made the scope. |
| `closingCompletes` | A call of closing on a herd by its owner is responded to, in time. |

The first is proven of `scopedWithCapability`'s tree and of the tree of the function it applies, gone through
in time: given its turn, the call reads the thread's scope and sets it, each responded to; the function it
applies, given its turn, applies the code to the scope; whatever that gave, it asks the scope for its herd, and
calls closing on it.

That closing completes is from two statements, each proven:

| Statement | Says |
|---|---|
| `closingCompletesOnceItsHerdEmpties` | A call of closing on a herd by its owner is responded to in time, if the herd's set comes to rest empty once closing has traversed it with no call adding to it in progress. |
| `aHerdsSetEmptiesOnceTraversed` | A herd's set comes to rest empty, once closing has traversed it with no call adding to it in progress. |

A set comes to rest empty when there are two moments, one from which nothing is in the set, and a later one at
which no call that was removing from it before the first is in progress.

The first of the two is from three statements, each proven:

| Statement | Says |
|---|---|
| `closingsTraversalsRespond` | A traversal of the herd's set that closing makes itself is responded to in time, once nothing more is added to the set. |
| `addingStopsOnceTheFlagIsSet` | From some moment on, nothing is added to the set of a herd whose flag is set. |
| `addingEndsOnceTheFlagIsSet` | From some moment on, no call that adds to the set of a herd whose flag is set is in progress. |

The first of these is from three statements, each proven: a call of a function closing has passed to a
traversal, on a thread that was added to the herd's set, is responded to in time (`closingsFunctionsRespond`); a
thread added to a herd's set runs, to its end and in time, the function a factory made it for, once it has been
interrupted (`aForkEndsOnceInterrupted`); and once the function that closing's functions apply to a thread has
completed, the thread has been interrupted (`whatClosingsFunctionsApplyInterrupts`).

That the set empties is from four statements, each proven:

| Statement | Says |
|---|---|
| `whatStaysInATraversedSetIsInterrupted` | A thread in a herd's set after closing has traversed it, with no call adding to it in progress, has been interrupted. |
| `anInterruptedForkLeavesForGood` | A thread added to a herd's set is out of it for good from some moment on, once it has been interrupted. |
| `addingStopsOnceTheFlagIsSet` | (above) |
| `addingEndsOnceTheFlagIsSet` | (above) |

A thread in the set after the traversal was in it throughout: it came in by a call that adds it, none was in
progress, and what leaves does not come back without one. So the traversal applied closing's function to it
(assumed of the JDK), and that function, gone through whole, interrupts the thread it is given
(`closingsFunctionsInterrupt`). An interrupted fork ends the function it was made for; that function, gone
through whole, asks for the current thread and removes it, by a call that is over when the function is
(`aForkFunctionRemovesItsThread`); the removal takes the thread out at a moment, and it does not come back,
since the one call that adds it was over before the thread was started (`startThreadStartsAfterItsAddIsOver`,
`aForkThatEndedStaysOut`). The threads to wait for are those in the set at one moment after the traversal: each
was added at a moment before it, a moment has one call, so they are finitely many, and there is a moment after
which each is out for good. A call that removes after that moment finds nothing to remove; those made before
it are finitely many and each is responded to.

## What stands, and on what

All fifteen roots are proven: every claim below each is proven, down to the trees of `unsupervised`, of
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

- That no thread is started (`noThreadIsStartedOnce…Ends`, `aClosedHerdRefusesToStart`), and so that a fork is
  refused (`fork…IsRefusedOnce…Ends`), rests on the JDK, the JVM and Scala's objects, and on one assumption
  about Ox, `aHerdKeepsItsFlagToItself`, and no more. The suite pins it.
- That no fork runs, that what a fork began is over, and that nothing is added (`noForkRunsOnce…`,
  `whatAForkBeganIsOverOnce…`, `nothingIsAddedOnce…`) rest, beside the platform, on every other kind below,
  and among them on `nothingIsAddedDuringTheLastCheck`, **which is false of Ox 1.1.0**: a defect that can be
  reproduced, for which its owner has a patch. They are proven from it, and hold of Ox once the patched code
  is what the model reads; of Ox 1.1.0 they are not shown.
- That a scope's herd is closed in time (`aScopesHerdIsClosedInTime`) rests on what is assumed to happen in
  time, and on the code a fork is given ending once interrupted; it does not rest on the assumption false of
  Ox 1.1.0.

Forty claims are proven of the code's trees, each gone through whole (the four of a scope among them). Three
are of what making a herd runs: a herd has been made, and its flag and its set are what `new AtomicBoolean(false)` and
`ConcurrentHashMap.newKeySet()` returned to the call that made it. Eight say what a piece of the herd's code calls
itself: one per method (`startThreadCallsFive`, `closingCallsFour`, `theClosingCheckCallsGet`,
`theTreeCheckCallsFour`, `theOwnerCheckCallsCurrentThread`, `theMembershipCheckCallsContains`), one for the function
`startThread` hands the factory (`theForkFunctionCallsFour`), and one for the function the tree check applies to go up
the scopes, which applies itself (`theWalkUpCallsFour`).

Forty-six claims are proven from the JDK, the JVM and Scala's objects alone, with no assumption
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

That a fork ends once interrupted is proven in three steps. A call of `startThread` that has added a thread
calls `start` on it in time (`startThreadStartsWhatItAdded`: each call it made before the add was responded
to, the add being seen; and it adds but once, `startThreadAddsOnce`). The thread then runs the function the
factory made it for (assumed of the factory and of who schedules threads). And that function, which is the one
written in `startThread`, ends once the code it calls does (`aForkFunctionCompletesOnceItsCodeDoes`): it calls
the code `startThread` was given, and then, whatever that gave, reads the set, asks for the current thread,
removes it and discards the answer. The code ends because it is assumed to, once its thread is interrupted.
Nothing here rests on the assumption that is false of Ox 1.1.0.

That closing has interrupted each thread it then joins is proven of closing's tree, three deep, with what
holds of the variable it keeps the threads it has interrupted in (`whatClosingsFunctionsApplyInterrupts`): every
set written there holds only threads that have been interrupted, by induction on when it is written. The function
closing's functions apply reads the variable; a thread it finds there has been interrupted, by what was last
written; one it does not find, it interrupts and writes among them.

That closing's functions are responded to is proven of the same tree (`closingsFunctionsRespond`). Each applies
the function that interrupts a thread once, which reads, interrupts, writes and returns, each step in time. The
second then joins the thread: the thread has been interrupted by then and was added to the herd's set, so it ends
the function it was made for, and the join is responded to (assumed of the JDK and of the thread factory, of a
thread whose function has ended). Whatever the join gave, the function ends.

That closing's traversals are responded to (`closingsTraversalsRespond`) is from that, and from what is assumed
of a traversal of a concurrent set: it is responded to once each call of its function is, if nothing more is
added; and it applies its function only to what is in the set at a moment while it runs. What is in a herd's set
was added during a call of `startThread` on the herd (`whatIsInAHerdsSetWasMadeToRun`: what is in a set was
added, and only `startThread` adds to a herd's set, while it runs), so closing's functions are responded to on
it.

That adding stops (`addingStopsOnceTheFlagIsSet`) is a count. A call that adds to the herd's set is one a call
of `startThread` on the herd makes itself; that call saw the flag unset at a moment during it, so it was made
before the flag was set, and after the execution began. There are finitely many moments in between, a moment
has one call, and a call of `startThread` adds but once: so there is a last add. A call that adds takes time,
and what it adds is in the set from a moment during it; each such call is responded to (assumed), and they are
finitely many, so from some moment on none is in progress (`addingEndsOnceTheFlagIsSet`).

That closing completes, on that condition (`closingCompletesOnceItsHerdEmpties`), is proven of closing's tree.
Given its turn, the call checks its caller (`theOwnerCheckResponds`, proven of that method's tree), sets the flag
and loops, and each call it makes is responded to. Once the flag is set adding stops, so each traversal is
responded to. A turn of the loop asks the set whether it is empty: on a yes the call ends; on a no it traverses
the set twice and comes to the next turn. Until adding ends there are finitely many moments, so finitely many
turns. A turn after that traverses the set with no call adding to it, so by the condition the set comes to rest
empty; until it rests there are finitely many turns again; and a turn after it is answered yes (assumed of the
JDK, of a set that holds nothing, once each call that was removing from it before it emptied is over).

What is assumed, by what it is about (each statement about the JDK is set beside what the JDK says, its
documentation or its code, in [`JDK.md`](JDK.md)):

- **The JDK and the JVM** (28): `addingIsAtomic`, `anElementLeavesOnlyWhenRemoved`,
  `isEmptyFindsItEmptyUnlessAdded`, `isEmptyReturns`, `getGivesTheFlag`, `settingIsAtomic`,
  `aFlagBecomesOnlyWhatIsSet`, `setReturns`, `currentThreadIsTheCaller`, `theJdkStaysOutOfHerds`,
  `whatTheChecksAskOfTheJdkStaysOutOfHerds`, `aThreadDoesOneThingAtATime`,
  `aTraversalThrowsOnlyWhatItsFunctionThrew`, `joinThrowsOnlyAnInterruption`, `interruptReturns`,
  `addSuppressedReturns`, `anAtomicBooleanHasOnlyItsMethods`, `aKeySetHasOnlyItsMethods`,
  `theCurrentScopeIsReadAndSet`, `aTraversalAppliesItsFunctionToElements` (a traversal applies its function
  only to what is in the set at a moment from its call to the application), `anElementWasAdded` (what is in a
  set is there by a call that adds it, and returns), `isEmptyFindsARestingSetEmpty` (a set that holds nothing
  from a moment on answers that it is empty to a call made once each call that was removing from it before that
  moment is over: `isEmpty` sums counters, and with those removals over each decrement has been counted; a
  removal made later finds nothing and counts nothing), `anElementEntersOnlyWhenAdded` (an element enters a
  set only at a moment during a call that adds it), `removingTakesTheElementOut` (a call that removes an object
  takes it out at one moment during the call, and nothing else), `aTraversalReachesWhatStays` (a traversal that
  returns has applied its function to each element that was in the set from its call to its return: the
  iteration is weakly consistent), `aThreadActsOnlyOnceStarted` (a thread a factory made makes no call before
  `start` is called on it), `currentThreadIsAnObject` (`Thread.currentThread()` gives no null),
  `aCallEndsAfterTheCallsItMade` (a call is responded to only once each call it made itself is over: a call
  returns to the call that made it).
- **Scala's objects** (7): `herdsAreConstructed`, `aHerdKeepsItsFields`, `aHerdHoldsWhatItWasGiven`,
  `aScopeHoldsTheHerdItIsMadeWith` (the `apply` the compiler writes for a case class is in no tree read: a scope
  made with a herd holds that herd), `aScopeIsConstructed` (and it is one that a call of the class's
  constructor has returned), `aScopeKeepsItsFields` (each val of a scope is read as what the scope holds),
  `aScopeGivesTheHerdItHolds` (a scope's herd is a val, asked for through the trait that declares it).
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
- **That a variable stays its call's** (2): `closingKeepsItsVariableToItself`. What a call of closing itself
  makes (the variable it keeps what interrupted it in, and the one it keeps the threads it has interrupted in),
  only the thread that called closing reads and writes. The functions closing hands its traversals hold the
  variables; the JDK's traversal applies them on the thread that called it and hands them to nothing.
  `closingsVariablesAreWrittenByItsFunctions`: and they are written only by such a function, or by the function
  it applies, itself. Both are assumed, and not derived from the code.
- **Who reaches a thread and the code startThread is given** (2): `onlyItsMakerStartsAThread`,
  `onlyAForkFunctionCallsTheCode`. These are statements about Ox, of a local value and of a parameter, not yet
  derived from its code.
- **Ox's scopes, which are not read** (1): `aScopesHerdAndParentStayOutOfHerds`. Asking a scope for its herd or
  its parent neither closes a herd nor removes from a herd's set. Both are vals of a scope; the classes of
  scopes are not read here, so this is an assumption about code of Ox, the one of its kind.
- **What happens in time** (20). Nothing happens in time unless it is assumed that threads are given their turn
  and that calls of what is outside the code are responded to: an execution in which every thread stops for
  good is one of the code. `aHerdsMethodsProceed`, `aForkFunctionProceeds`: a call of this code that is pending
  and waits for no call it made makes its next event (`aHerdsMethodsProceed` is of every method of a herd).
  `currentThreadResponds`, `removingResponds`,
  `discardResponds`: a call is responded to. `aStartedThreadRunsItsFunction`: a thread a factory made for a
  function calls the function, once `start` is called on it (of the thread factory, and of who schedules
  threads).
  `closingsFunctionsProceed`, `whatClosingsFunctionsApplyProceeds`: the same of a function closing has passed
  to a traversal, and of the function it applies. `interruptResponds`, `addSuppressedResponds`: a call is
  responded to. `joinRespondsOnceItsThreadHasRun`: a call of join on a thread a factory made for a function is
  responded to, once the thread's call of the function has been (of the JDK and of the thread factory: the
  thread ends when the function does). `aTraversalRespondsOnceItsFunctionDoes`: a traversal of a concurrent set
  to which nothing more is added is responded to, if each call of its function that it itself makes is.
  `theExecutionBegins`: nothing is called before the execution begins (an execution has a first moment).
  `settingResponds`, `isEmptyResponds`, `addingResponds`: a call that sets an atomic boolean, one that asks a
  set whether it is empty, and one that adds to a set, is responded to. `runningInAScopeProceeds`,
  `whatRunningInAScopeAppliesProceeds`: a call running code in a scope, and a call of a function it itself
  makes, proceed. `theCurrentScopeResponds`, `aScopesHerdResponds`: reading a thread's current scope, setting
  it, and asking a scope for its herd are responded to.
- **The code a fork is given** (1): `forkCodeCompletesOnceInterrupted`. The code a fork was made to run is
  responded to in time, once the fork has been interrupted, whenever that was. It is a restriction on who uses
  Ox: code that ignores interruption and never ends keeps its scope from ending. And it takes something of the
  JVM: closing can interrupt a thread before it is started, and the JDK's documentation lets such an
  interruption be lost; OpenJDK keeps it (`JDK.md`).
- **Ox itself, false of Ox 1.1.0** (1): `nothingIsAddedDuringTheLastCheck`. `isEmpty` on a concurrent set is no
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

- The supervisor and the scope's finalizers: they are not read. Of the functions that start a fork, the file is
  read, and six are gone through, up to their call of `startThread`: `forkUnsupervised`, `forkCancellable`,
  `fork`, `forkUser`, `forkError` and `forkUserError`. Nothing is claimed of `forkAll`, which forks by `fork`,
  of what the function handed to `startThread` does, nor of what a fork's `join` gives. Nothing is said of what
  `supervised` returns.
- That closing completes is of a herd whose forks end once interrupted: that the code a fork was made to run is
  responded to in time once the fork has been interrupted is assumed of that code
  (`forkCodeCompletesOnceInterrupted`), and shown of none. A fork that swallows the interruption and goes on
  keeps closing waiting, in Ox as in the model.
- That `unsupervised` and `supervised` complete. What is proven is the middle: running code in a scope comes
  to closing the scope's herd once the code has ended, and closing completes. Not proven: that the call comes to
  running code in the scope (making the scope, and for `supervised` its supervisor, is responded to), that the
  code given to `supervised`'s scope ends (it waits for the supervisor), and that what follows closing ends (the
  scope's finalizers, which are the user's code, run uninterruptibly).
- That no run of Ox's code has a data race. The model takes it that the events of threads come one after
  another, which the JVM grants only to a program without one (JLS 17.4.5). It was proven of a herd in a
  separation logic over the machine, which is removed with the proofs it was unconnected to; it is to be proven
  over executions.
- The link to the JVM is a theorem and a test. The theorem (`FrFlow/Code/Executed.v`, `machine_conforms`): the
  events a run of the machine writes out (`FrFlow/Code/Frames.v`) are an execution in the model's sense, for any
  code, any library of what is outside it and any order of the threads' turns; the machine stops where a step
  would not be one an execution has. The test: 25 programs written against Ox are run on that machine and give
  what they give on the JVM, none stopping (`rocq/Ox/README.md`). Not proven: that the machine does what the
  JVM does; and the runs are over the whole of Ox, where the model's statements are of the files it reads with
  the rest of Ox outside them. What the model assumes of the JDK is not derived from the library the machine
  runs for it; it rests on the JDK's documentation.
- That a value of a class of the JDK, or of a class of Ox that no object the code names is of, is no Scala
  `object`: assumed of what calls the code (`Conforms.of_class`). The classes that have an object among their
  values (`ox.ErrorMode`, `ox.Supervisor` among them) are read from the code.
- What is built on scopes (`par`, `race`, `timeout`, cancellation, error modes, `ForkLocal`), channels, `Flow`,
  retries and scheduling, actors.
- That the statements at the bottom can hold together is shown by one execution, in which a thread makes a herd
  and closes it (`rocq/Proofs/OxThreads/Whole.v`): its 27 events are written out, each of its three calls is
  shown to follow the code read from Ox, event by event, and each of the 70 statements is shown of it. It has
  no fork, no thread started and no scope: of what is assumed of those it shows only that it does not
  contradict what happens to a herd alone. An execution with a fork is the next one to write out. That each
  step's parts can hold together is still shown by the execution in which nothing happens; it follows from the
  whole's and the steps, which a proof file may not use.

## Checking it

```bash
sbt "oxModel/Rocq/testOnly ox.threads.ThreadsSuite"
```
