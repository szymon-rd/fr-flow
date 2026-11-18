package ox.threads

import frflow.*
import frflow.code.Read
import frflow.executions.*
import ox.internal.ThreadHerd
import ox.live.*
import ox.scopes.*

// The model of Ox's threads: what holds once `unsupervised` or `supervised` has completed (the roots), by what
// holds once a herd is closed, and what makes that hold. That no thread is started rests on the herd's flag
// alone; the other two, on who starts a thread. All of it is of Ox's code as its jar has it.

// What holds once a scope's call has completed, and of a herd once closed.
private val once: List[FrModel.Part] = List(
  everyForkHasLeftOnceClosed, codeRunsBeforeLeaving, onlyAForkFunctionCallsTheCode, aThreadRunsOneForkFunctionOnce,
  aForkFunctionRemovesAfterTheCode,

  closingEndsOnEmpty, closingEndsOnceFoundEmpty, isEmptyFindsItEmptyUnlessAdded, nothingIsAddedDuringTheLastCheck,
  isEmptyReturns, closingsTraversalsReturn, aTraversalThrowsOnlyWhatItsFunctionThrew, closingTraversesWithAFunction,
  closingsFunctionsReturn, whatClosingsFunctionsApplyReturns, closingKeepsItsVariableToItself,
  closingsVariablesAreWrittenByItsFunctions, joinThrowsOnlyAnInterruption, addSuppressedReturns, interruptReturns,
  nothingIsAddedOnceEmpty, nothingIsBeingAddedWhenEmpty, liveForksAreInTheSet, whoAddsIsCallingStartThread,

  startThreadCallersStayInside, onlyStartThreadAdds,

  startThreadIsCalledFromInside, startThreadStaysOutOfHerds, aForkRemovesOnlyItself,

  closingSetsTheFlag, theFlagStaysSet, aFlagBecomesOnlyWhatIsSet, aHerdsFlagIsOnlyReadAndSet, onlyClosingSetsTheFlag,
  closingSetsTheFlagOnlyToTrue,

  // What a herd keeps to itself: its flag.
  aHerdKeepsItsFlagToItself, anAtomicBooleanHasOnlyItsMethods, aHerdsMethodsOnlyGetAndSetAFlag, closingCallsFour,
  theOwnerCheckCallsCurrentThread, theMembershipCheckCallsContains, startThreadFirstSeesTheFlagUnset,

  // What a herd keeps to itself: its set.
  aHerdKeepsItsSetToItself, aKeySetHasOnlyItsMethods, whatAHerdsCodeCallsOfASet, theForkFunctionCallsFour,

  startThreadReadsTheFlagUnset, getGivesTheFlag, closingSetsTheFlagItself, settingIsAtomic, setReturns,

  onlyStartThreadAddsToTheSet, startThreadAddsWhileItRuns, startThreadIsPendingWhileItAdds,
  anAddedThreadHasNotBeenStarted, onlyItsMakerStartsAThread, startThreadAddsWhatItsFactoryMade,
  startThreadAddsBeforeItStarts,

  onlyAForkFunctionRemoves, theForkFunctionRemovesTheCurrentThread,

  startThreadCallsFive, theClosingCheckStaysOutOfHerds, theTreeCheckStaysOutOfHerds, aFactoryStaysOutOfHerds,
  theClosingCheckCallsGet, theTreeCheckCallsFour, theJdkStaysOutOfHerds,

  // The tree check, and the function it applies to go up the scopes.
  theWalkUpStaysOutOfHerds, whatTheChecksAskOfTheJdkStaysOutOfHerds, theWalkUpCallsFour,
  aScopesHerdAndParentStayOutOfHerds, theMembershipCheckStaysOutOfHerds, aThreadDoesOneThingAtATime,

  // How a herd is made.
  herdsAreConstructed, aHerdsFlagIsNew, aHerdsSetIsNew, aHerdHoldsWhatItWasGiven,

  herdsAreMade, aHerdKeepsItsFields, currentThreadIsTheCaller,

  addingIsAtomic, anElementLeavesOnlyWhenRemoved, aHerdsSetIsPlain,

  // The execution is one of Ox's `ThreadHerd`, of its scopes, of `unsupervised` and of `supervised`, as its jar
  // has them.
  history.executing(Read.of(classOf[ThreadHerd], Set("ox/internal/ThreadHerd.tasty", "ox/OxError.tasty",
    "ox/unsupervised$package.tasty", "ox/supervised$package.tasty", "ox/fork$package.tasty"))))

val oxThreads: FrModel =
  FrModel("OxThreads")((roots ++ withoutRaces ++ scopesWithoutRaces ++ inTime ++ ofScopes ++ once)*)
