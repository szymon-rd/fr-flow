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

Every step from parts to a claim that has a proof is proven. Thirteen claims are proven of the code's trees.
Four claims are not proven; FrFlow reports them so, and every node above one of them as waiting, and the suite
names them (`ThreadsSuite`):

| Not proven | Below |
|---|---|
| `aHerdsFlagIsOnlyReadAndSet` | `aClosedHerdRefusesToStart` |
| `aHerdsSetIsPlain` | the first two roots |
| `closingsTraversalsReturn` | the first two roots |
| `theTreeCheckStaysOutOfHerds` | the first two roots |

Of the last, what the check calls itself is proven (`theTreeCheckCallsFour`); the function it applies calls
into scopes, which are not read.

What is assumed, by what it is about:

- **The JDK and the JVM** (11): `addingIsAtomic`, `anElementLeavesOnlyWhenRemoved`,
  `isEmptyFindsItEmptyUnlessAdded`, `isEmptyReturns`, `getGivesTheFlag`, `settingIsAtomic`,
  `aFlagBecomesOnlyWhatIsSet`, `setReturns`, `currentThreadIsTheCaller`, `theJdkStaysOutOfHerds`,
  `aThreadDoesOneThingAtATime`.
- **Scala's objects** (2): `herdsAreMade`, `aHerdKeepsItsFields`.
- **Who uses a herd** (1): `startThreadIsCalledFromInside`. It is stricter than Ox's own check: it leaves out a
  fork of a nested scope starting a fork in an enclosing one.
- **The thread factory a herd is given** (2): `aThreadRunsOneForkFunctionOnce`, `aFactoryStaysOutOfHerds`.
- **Who reaches what the herd keeps private** (5): `onlyStartThreadAddsToTheSet`, `onlyItsMakerStartsAThread`,
  `onlyAForkFunctionRemoves`, `onlyAForkFunctionCallsTheCode`, `onlyClosingSetsTheFlag`. These are statements
  about Ox, not yet derived from its code and a rule of the language.
- **Ox itself, suspected false** (1): `nothingIsAddedDuringTheLastCheck`. `isEmpty` on a concurrent set is no
  snapshot; a fork that starts another and leaves while closing asks can make it answer yes of a set that was
  never empty. The first two roots rest on it.

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
