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

private val roots: List[FrModel.Part] = List(
  noForkRunsOnceUnsupervisedEnds, nothingIsAddedOnceUnsupervisedEnds, noThreadIsStartedOnceUnsupervisedEnds,
  noForkRunsOnceSupervisedEnds, nothingIsAddedOnceSupervisedEnds, noThreadIsStartedOnceSupervisedEnds,
  whatAForkBeganIsOverOnceUnsupervisedEnds, whatAForkBeganIsOverOnceSupervisedEnds,
  forkUnsupervisedIsRefusedOnceUnsupervisedEnds, forkUnsupervisedIsRefusedOnceSupervisedEnds,
  forkIsRefusedOnceSupervisedEnds,
  aScopesHerdIsClosedInTime, closingCompletes.refines(aScopesHerdIsClosedInTime),
  closingCompletesOnceItsHerdEmpties.refines(closingCompletes),
  aScopesClosingIsReached.refines(aScopesHerdIsClosedInTime),
  runningInAScopeProceeds.refines(aScopesClosingIsReached),
  whatRunningInAScopeAppliesProceeds.refines(aScopesClosingIsReached),
  theCurrentScopeResponds.refines(aScopesClosingIsReached), aScopesHerdResponds.refines(aScopesClosingIsReached))

// What holds once a scope's call has completed, and of a herd once closed.
private val once: List[FrModel.Part] = List(
  // A scope: `unsupervised` and `supervised` make one, run code in it, and its herd is closed before they end.
  unsupervisedClosesItsScopesHerd.refines(noForkRunsOnceUnsupervisedEnds, nothingIsAddedOnceUnsupervisedEnds,
    noThreadIsStartedOnceUnsupervisedEnds, whatAForkBeganIsOverOnceUnsupervisedEnds,
    forkUnsupervisedIsRefusedOnceUnsupervisedEnds),
  supervisedClosesItsScopesHerd.refines(noForkRunsOnceSupervisedEnds, nothingIsAddedOnceSupervisedEnds,
    noThreadIsStartedOnceSupervisedEnds, whatAForkBeganIsOverOnceSupervisedEnds,
    forkUnsupervisedIsRefusedOnceSupervisedEnds, forkIsRefusedOnceSupervisedEnds),
  forkUnsupervisedIsRefusedOnceClosed.refines(forkUnsupervisedIsRefusedOnceUnsupervisedEnds,
    forkUnsupervisedIsRefusedOnceSupervisedEnds),
  forkUnsupervisedStartsAThread.refines(forkUnsupervisedIsRefusedOnceClosed),
  forkStartsAThread.refines(forkIsRefusedOnceSupervisedEnds),
  aScopeMadeIsAnObject.refines(forkIsRefusedOnceSupervisedEnds),
  forkErrorStartsAThread.refines(forkStartsAThread), asNoErrorModeKeepsTheHerd.refines(forkStartsAThread),
  aConstructedScopeIsMade.refines(aScopeMadeIsAnObject, asNoErrorModeKeepsTheHerd),
  aScopeIsConstructed.refines(aScopeMadeIsAnObject, asNoErrorModeKeepsTheHerd),
  aScopeKeepsItsFields.refines(asNoErrorModeKeepsTheHerd, forkErrorStartsAThread),
  whatAForkBeganIsOverOnceClosed.refines(whatAForkBeganIsOverOnceUnsupervisedEnds,
    whatAForkBeganIsOverOnceSupervisedEnds),
  noForkRunsOnceClosed.refines(noForkRunsOnceUnsupervisedEnds, noForkRunsOnceSupervisedEnds,
    whatAForkBeganIsOverOnceClosed),
  callsNest.refines(whatAForkBeganIsOverOnceClosed), aCallEndsAfterTheCallsItMade.refines(callsNest),
  nothingIsAddedOnceClosed.refines(nothingIsAddedOnceUnsupervisedEnds, nothingIsAddedOnceSupervisedEnds),
  aClosedHerdRefusesToStart.refines(noThreadIsStartedOnceUnsupervisedEnds, noThreadIsStartedOnceSupervisedEnds,
    forkUnsupervisedIsRefusedOnceClosed, forkIsRefusedOnceSupervisedEnds),
  unsupervisedRunsInTheScopeItMade.refines(unsupervisedClosesItsScopesHerd),
  supervisedRunsInTheScopeItMade.refines(supervisedClosesItsScopesHerd),
  aScopeEndsAfterItsHerdIsClosed.refines(unsupervisedClosesItsScopesHerd, supervisedClosesItsScopesHerd),
  aScopesHerdIsItsMakers.refines(unsupervisedClosesItsScopesHerd, supervisedClosesItsScopesHerd,
    aScopesHerdIsClosedInTime),
  aScopeGivesTheHerdItHolds.refines(aScopeEndsAfterItsHerdIsClosed, aScopesClosingIsReached,
    forkUnsupervisedStartsAThread),
  theCurrentScopeIsReadAndSet.refines(aScopeEndsAfterItsHerdIsClosed, aScopesClosingIsReached),
  aScopeHoldsTheHerdItIsMadeWith.refines(aScopesHerdIsItsMakers, asNoErrorModeKeepsTheHerd),

  everyForkHasLeftOnceClosed.refines(noForkRunsOnceClosed),
  codeRunsBeforeLeaving.refines(noForkRunsOnceClosed),
  onlyAForkFunctionCallsTheCode.refines(codeRunsBeforeLeaving),
  aThreadRunsOneForkFunctionOnce.refines(codeRunsBeforeLeaving),
  aForkFunctionRemovesAfterTheCode.refines(codeRunsBeforeLeaving),

  closingEndsOnEmpty.refines(everyForkHasLeftOnceClosed, nothingIsAddedOnceClosed),
  closingEndsOnceFoundEmpty.refines(closingEndsOnEmpty),
  isEmptyFindsItEmptyUnlessAdded.refines(closingEndsOnEmpty),
  nothingIsAddedDuringTheLastCheck.refines(closingEndsOnEmpty),
  isEmptyReturns.refines(closingEndsOnceFoundEmpty),
  closingsTraversalsReturn.refines(closingEndsOnceFoundEmpty, whatStaysInATraversedSetIsInterrupted),
  aTraversalThrowsOnlyWhatItsFunctionThrew.refines(closingsTraversalsReturn),
  closingTraversesWithAFunction.refines(closingsTraversalsReturn),
  closingsFunctionsReturn.refines(closingsTraversalsReturn),
  whatClosingsFunctionsApplyReturns.refines(closingsFunctionsReturn),
  closingKeepsItsVariableToItself.refines(closingsFunctionsReturn, whatClosingsFunctionsApplyInterrupts),
  closingsVariablesAreWrittenByItsFunctions.refines(whatClosingsFunctionsApplyInterrupts),
  joinThrowsOnlyAnInterruption.refines(closingsFunctionsReturn, whatClosingsFunctionsApplyReturns,
    whatClosingsFunctionsApplyInterrupts, closingsFunctionsRespond, closingsFunctionsInterrupt),
  addSuppressedReturns.refines(closingsFunctionsReturn),
  interruptReturns.refines(whatClosingsFunctionsApplyReturns, whatClosingsFunctionsApplyInterrupts),
  nothingIsAddedOnceEmpty.refines(everyForkHasLeftOnceClosed, nothingIsAddedOnceClosed),
  nothingIsBeingAddedWhenEmpty.refines(everyForkHasLeftOnceClosed, nothingIsAddedOnceEmpty),
  liveForksAreInTheSet.refines(everyForkHasLeftOnceClosed, nothingIsAddedOnceEmpty, nothingIsBeingAddedWhenEmpty),
  whoAddsIsCallingStartThread.refines(nothingIsBeingAddedWhenEmpty),

  startThreadCallersStayInside.refines(nothingIsAddedOnceEmpty, nothingIsBeingAddedWhenEmpty),
  onlyStartThreadAdds.refines(nothingIsAddedOnceEmpty),

  startThreadIsCalledFromInside.refines(startThreadCallersStayInside),
  startThreadStaysOutOfHerds.refines(startThreadCallersStayInside),
  aForkRemovesOnlyItself.refines(startThreadCallersStayInside, codeRunsBeforeLeaving),

  closingSetsTheFlag.refines(aClosedHerdRefusesToStart),
  theFlagStaysSet.refines(aClosedHerdRefusesToStart, closingSetsTheFlag, addingStopsOnceTheFlagIsSet),
  aFlagBecomesOnlyWhatIsSet.refines(theFlagStaysSet), aHerdsFlagIsOnlyReadAndSet.refines(theFlagStaysSet),
  onlyClosingSetsTheFlag.refines(theFlagStaysSet),
  closingSetsTheFlagOnlyToTrue.refines(theFlagStaysSet),

  // What a herd keeps to itself: its flag.
  aHerdKeepsItsFlagToItself.refines(aHerdsFlagIsOnlyReadAndSet, onlyClosingSetsTheFlag),
  anAtomicBooleanHasOnlyItsMethods.refines(aHerdsFlagIsOnlyReadAndSet),
  aHerdsMethodsOnlyGetAndSetAFlag.refines(aHerdsFlagIsOnlyReadAndSet, onlyClosingSetsTheFlag),
  closingCallsFour.refines(aHerdsMethodsOnlyGetAndSetAFlag, whatAHerdsCodeCallsOfASet),
  theOwnerCheckCallsCurrentThread.refines(aHerdsMethodsOnlyGetAndSetAFlag, whatAHerdsCodeCallsOfASet),
  theMembershipCheckCallsContains.refines(aHerdsMethodsOnlyGetAndSetAFlag, whatAHerdsCodeCallsOfASet,
    theMembershipCheckStaysOutOfHerds),
  startThreadFirstSeesTheFlagUnset.refines(aClosedHerdRefusesToStart, addingStopsOnceTheFlagIsSet),

  // What a herd keeps to itself: its set.
  aHerdKeepsItsSetToItself.refines(aHerdsSetIsPlain, onlyStartThreadAddsToTheSet, onlyAForkFunctionRemoves),
  aKeySetHasOnlyItsMethods.refines(aHerdsSetIsPlain),
  whatAHerdsCodeCallsOfASet.refines(aHerdsSetIsPlain, onlyStartThreadAddsToTheSet, onlyAForkFunctionRemoves),
  theForkFunctionCallsFour.refines(whatAHerdsCodeCallsOfASet),

  startThreadReadsTheFlagUnset.refines(startThreadFirstSeesTheFlagUnset),
  getGivesTheFlag.refines(startThreadFirstSeesTheFlagUnset),
  closingSetsTheFlagItself.refines(closingSetsTheFlag),
  settingIsAtomic.refines(closingSetsTheFlag, closingCompletesOnceItsHerdEmpties),
  setReturns.refines(closingEndsOnceFoundEmpty, closingSetsTheFlag),

  onlyStartThreadAddsToTheSet.refines(onlyStartThreadAdds, anAddedThreadHasNotBeenStarted,
    whoAddsIsCallingStartThread, aForkEndsOnceInterrupted, whatIsInAHerdsSetWasMadeToRun,
    addingStopsOnceTheFlagIsSet, anInterruptedForkLeavesForGood, aForkThatEndedStaysOut),
  startThreadAddsWhileItRuns.refines(onlyStartThreadAdds, whoAddsIsCallingStartThread, aForkEndsOnceInterrupted,
    whatIsInAHerdsSetWasMadeToRun, anInterruptedForkLeavesForGood),
  startThreadIsPendingWhileItAdds.refines(whoAddsIsCallingStartThread),
  anAddedThreadHasNotBeenStarted.refines(onlyStartThreadAdds, aForkThatEndedStaysOut),
  onlyItsMakerStartsAThread.refines(anAddedThreadHasNotBeenStarted, aForkThatEndedStaysOut),
  startThreadAddsWhatItsFactoryMade.refines(anAddedThreadHasNotBeenStarted, aForkEndsOnceInterrupted,
    anInterruptedForkLeavesForGood, aForkThatEndedStaysOut),
  startThreadAddsBeforeItStarts.refines(anAddedThreadHasNotBeenStarted, aForkThatEndedStaysOut),

  onlyAForkFunctionRemoves.refines(aForkRemovesOnlyItself, codeRunsBeforeLeaving),
  theForkFunctionRemovesTheCurrentThread.refines(aForkRemovesOnlyItself),

  startThreadCallsFive.refines(startThreadStaysOutOfHerds, aHerdsMethodsOnlyGetAndSetAFlag,
    whatAHerdsCodeCallsOfASet),
  theClosingCheckStaysOutOfHerds.refines(startThreadStaysOutOfHerds),
  theTreeCheckStaysOutOfHerds.refines(startThreadStaysOutOfHerds),
  aFactoryStaysOutOfHerds.refines(startThreadStaysOutOfHerds),
  theClosingCheckCallsGet.refines(theClosingCheckStaysOutOfHerds, aHerdsMethodsOnlyGetAndSetAFlag,
    whatAHerdsCodeCallsOfASet),
  theTreeCheckCallsFour.refines(theTreeCheckStaysOutOfHerds, aHerdsMethodsOnlyGetAndSetAFlag,
    whatAHerdsCodeCallsOfASet),
  theJdkStaysOutOfHerds.refines(startThreadStaysOutOfHerds, theClosingCheckStaysOutOfHerds),

  // The tree check, and the function it applies to go up the scopes.
  theWalkUpStaysOutOfHerds.refines(theTreeCheckStaysOutOfHerds),
  whatTheChecksAskOfTheJdkStaysOutOfHerds.refines(theTreeCheckStaysOutOfHerds, theMembershipCheckStaysOutOfHerds),
  theWalkUpCallsFour.refines(theWalkUpStaysOutOfHerds),
  aScopesHerdAndParentStayOutOfHerds.refines(theWalkUpStaysOutOfHerds),
  theMembershipCheckStaysOutOfHerds.refines(theWalkUpStaysOutOfHerds),
  aThreadDoesOneThingAtATime.refines(startThreadStaysOutOfHerds, theClosingCheckStaysOutOfHerds,
    closingsFunctionsReturn, theTreeCheckStaysOutOfHerds, theMembershipCheckStaysOutOfHerds,
    theWalkUpStaysOutOfHerds, callsNest),

  // How a herd is made.
  herdsAreConstructed.refines(herdsAreMade, closingSetsTheFlag, aClosedHerdRefusesToStart, nothingIsAddedOnceEmpty,
    aForkEndsOnceInterrupted, closingsTraversalsRespond, closingCompletesOnceItsHerdEmpties,
    nothingIsBeingAddedWhenEmpty, everyForkHasLeftOnceClosed, startThreadCallersStayInside, codeRunsBeforeLeaving,
    anInterruptedForkLeavesForGood, closingCompletes),
  aHerdsFlagIsNew.refines(aHerdsFlagIsOnlyReadAndSet), aHerdsSetIsNew.refines(aHerdsSetIsPlain),
  aHerdHoldsWhatItWasGiven.refines(aHerdsFlagIsNew, aHerdsSetIsNew, aScopesHerdIsItsMakers),

  herdsAreMade.refines(startThreadReadsTheFlagUnset, closingSetsTheFlagItself,
    theForkFunctionRemovesTheCurrentThread, startThreadAddsWhileItRuns, startThreadAddsWhatItsFactoryMade,
    startThreadAddsBeforeItStarts, closingEndsOnceFoundEmpty, closingSetsTheFlagOnlyToTrue,
    startThreadIsPendingWhileItAdds, theForkFunctionCallsFour,
    aForkFunctionRemovesAfterTheCode, startThreadCallsFive, theClosingCheckCallsGet, theTreeCheckCallsFour,
    closingTraversesWithAFunction, whatClosingsFunctionsApplyReturns, closingsFunctionsReturn,
    closingCallsFour, theOwnerCheckCallsCurrentThread, theMembershipCheckCallsContains, theWalkUpCallsFour,
    aForkFunctionCompletesOnceItsCodeDoes, startThreadAddsOnce, startThreadStartsWhatItAdded,
    whatClosingsFunctionsApplyInterrupts, closingsFunctionsRespond, theOwnerCheckResponds,
    closingCompletesOnceItsHerdEmpties, closingsFunctionsInterrupt,
    aForkFunctionRemovesItsThread, startThreadStartsAfterItsAddIsOver),
  aHerdKeepsItsFields.refines(startThreadReadsTheFlagUnset, closingSetsTheFlagItself,
    theForkFunctionRemovesTheCurrentThread, closingEndsOnceFoundEmpty, closingCompletesOnceItsHerdEmpties,
    aForkFunctionRemovesItsThread),
  currentThreadIsTheCaller.refines(closingSetsTheFlagItself, aForkRemovesOnlyItself, closingEndsOnceFoundEmpty,
    aScopesHerdIsItsMakers, aForkFunctionRemovesItsThread),

  addingIsAtomic.refines(liveForksAreInTheSet), anElementLeavesOnlyWhenRemoved.refines(liveForksAreInTheSet),
  aHerdsSetIsPlain.refines(liveForksAreInTheSet, whatIsInAHerdsSetWasMadeToRun, aHerdsSetEmptiesOnceTraversed,
    whatStaysInATraversedSetIsInterrupted, aForkThatEndedStaysOut),

  // The execution is one of Ox's `ThreadHerd`, of its scopes, of `unsupervised` and of `supervised`, as its jar
  // has them.
  history.executing(Read.of(classOf[ThreadHerd], Set("ox/internal/ThreadHerd.tasty", "ox/OxError.tasty",
    "ox/unsupervised$package.tasty", "ox/supervised$package.tasty", "ox/fork$package.tasty"))))

val oxThreads: FrModel = FrModel("OxThreads")((roots ++ inTime ++ once)*)
