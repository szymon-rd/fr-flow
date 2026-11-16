# Ox's threads: what is proven of `ThreadHerd`

A FrFlow model of the class Ox keeps a scope's threads in, `ox.internal.ThreadHerd`. The code is read from Ox's
jar as it is compiled (its TASTy), unchanged. The statements are Scala (`src/main/scala/ox/threads`); each step is
proven in Rocq (`rocq/Proofs/OxThreads`), the claims at the bottom against the trees read.

## What is stated

Three roots, each of a herd after `interruptAllAndJoinUntilCompleted` (closing) has returned:

| Root | Says |
|---|---|
| `noForkRunsOnceClosed` | No fork of the herd runs the code it was made to run. |
| `nothingIsAddedOnceClosed` | No thread is added to the herd's set. |
| `aClosedHerdRefusesToStart` | A call of `startThread` does not return, and adds no thread. |

## What stands, and on what

The third root, `aClosedHerdRefusesToStart`, is proven: every claim below it is, down to `ThreadHerd`'s trees.
It rests on ten assumptions: nine about the JDK, the JVM and Scala's objects, and one about Ox,
`aHerdKeepsItsFlagToItself` (below). The suite pins the ten (`ThreadsSuite`).

The first two roots are not proven. Every step from parts to a claim that has a proof is proven; two claims
are not, FrFlow reports them so, and every node above one of them as waiting, and the suite names them:

| Not proven | Below |
|---|---|
| `closingsFunctionsReturn` | the first two roots |
| `theTreeCheckStaysOutOfHerds` | the first two roots |

Of the last, what the check calls itself is proven (`theTreeCheckCallsFour`); the function it applies calls
into scopes, which are not read. Of the one before, that closing's traversals do not throw is proven from it
(`closingsTraversalsReturn`), and so is that the function its two functions apply to interrupt a thread returns
(`whatClosingsFunctionsApplyReturns`); what is left is that the second function, catching an interruption,
reads a local variable twice: that the second read finds what the first did is not yet said of an execution.

Twenty-two claims are proven of the code's trees, each gone through whole. Three are of what making a herd
runs: a herd has been made, and its flag and its set are what `new AtomicBoolean(false)` and
`ConcurrentHashMap.newKeySet()` returned to the call that made it. Seven say what a piece of the herd's code
calls itself: one per method (`startThreadCallsFive`, `closingCallsFour`, `theClosingCheckCallsGet`,
`theTreeCheckCallsFour`, `theOwnerCheckCallsCurrentThread`, `theMembershipCheckCallsContains`), and one for the
function `startThread` hands the factory (`theForkFunctionCallsFour`).

Twenty-five claims are proven of Ox's code from the JDK, the JVM and Scala's objects alone, with no
assumption about Ox or about who uses it (the suite computes the list and pins it). Among them:

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
- `theClosingCheckStaysOutOfHerds`: a thread in `assertNotShuttingDown` neither closes a herd nor removes from
  a herd's set.

What is assumed, by what it is about:

- **The JDK and the JVM** (17): `addingIsAtomic`, `anElementLeavesOnlyWhenRemoved`,
  `isEmptyFindsItEmptyUnlessAdded`, `isEmptyReturns`, `getGivesTheFlag`, `settingIsAtomic`,
  `aFlagBecomesOnlyWhatIsSet`, `setReturns`, `currentThreadIsTheCaller`, `theJdkStaysOutOfHerds`,
  `aThreadDoesOneThingAtATime`, `aTraversalThrowsOnlyWhatItsFunctionThrew`, `joinThrowsOnlyAnInterruption`,
  `interruptReturns`, `addSuppressedReturns`, `anAtomicBooleanHasOnlyItsMethods`, `aKeySetHasOnlyItsMethods`.
- **Scala's objects** (3): `herdsAreConstructed`, `aHerdKeepsItsFields`, `aHerdHoldsWhatItWasGiven`.
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
- **Who reaches a thread and the code startThread is given** (2): `onlyItsMakerStartsAThread`,
  `onlyAForkFunctionCallsTheCode`. These are statements about Ox, of a local value and of a parameter, not yet
  derived from its code.
- **Ox itself, suspected false** (1): `nothingIsAddedDuringTheLastCheck`. `isEmpty` on a concurrent set is no
  snapshot; a fork that starts another and leaves while closing asks can make it answer yes of a set that was
  never empty. The first two roots rest on it; the third does not.

A call of an inline method (`discard`, in the function `startThread` hands the factory) is, in the tree read
from TASTy, a call: the model has it as a call of a method outside the code, where the JVM runs its expansion
in place.

Beside the nodes, three things are taken of Scala and the JVM: what an execution of the code is (the meaning of
its trees in Rocq, written by hand and tested against the JVM, `docs/EXECUTIONS.md`); that the events of
threads come one after another; and that the VM raises no error of its own.

## What is not covered

- The scopes above a herd: `unsupervised`, `fork`, `supervised`. So nothing here is yet about a scope, and
  nothing about what `supervised` returns.
- That anything completes: closing, a scope, `supervised`.
- What is built on scopes (`par`, `race`, `timeout`, cancellation, error modes, `ForkLocal`), channels, `Flow`,
  retries and scheduling, actors.
- Every witness that the statements can hold together is the execution in which nothing happens.

## Checking it

```bash
sbt "oxModel/Rocq/testOnly ox.threads.ThreadsSuite"
```
