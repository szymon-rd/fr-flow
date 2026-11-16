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

val oxThreads: FrModel = FrModel("OxThreads")(
  noForkRunsOnceUnsupervisedEnds, nothingIsAddedOnceUnsupervisedEnds, noThreadIsStartedOnceUnsupervisedEnds,
  noForkRunsOnceSupervisedEnds, nothingIsAddedOnceSupervisedEnds, noThreadIsStartedOnceSupervisedEnds,
  aForkEndsOnceInterrupted, whatClosingsFunctionsApplyInterrupts,

  // What happens in time: a fork ends once interrupted.
  startThreadStartsWhatItAdded.refines(aForkEndsOnceInterrupted),
  aStartedThreadRunsItsFunction.refines(aForkEndsOnceInterrupted),
  aForkFunctionCompletesOnceItsCodeDoes.refines(aForkEndsOnceInterrupted),
  forkCodeCompletesOnceInterrupted.refines(aForkEndsOnceInterrupted),
  startThreadAddsOnce.refines(startThreadStartsWhatItAdded),
  aHerdsMethodsProceed.refines(startThreadStartsWhatItAdded),
  aForkFunctionProceeds.refines(aForkFunctionCompletesOnceItsCodeDoes),
  currentThreadResponds.refines(aForkFunctionCompletesOnceItsCodeDoes),
  removingResponds.refines(aForkFunctionCompletesOnceItsCodeDoes),
  discardResponds.refines(aForkFunctionCompletesOnceItsCodeDoes),

  // A scope: `unsupervised` and `supervised` make one, run code in it, and its herd is closed before they end.
  unsupervisedClosesItsScopesHerd.refines(noForkRunsOnceUnsupervisedEnds, nothingIsAddedOnceUnsupervisedEnds,
    noThreadIsStartedOnceUnsupervisedEnds),
  supervisedClosesItsScopesHerd.refines(noForkRunsOnceSupervisedEnds, nothingIsAddedOnceSupervisedEnds,
    noThreadIsStartedOnceSupervisedEnds),
  noForkRunsOnceClosed.refines(noForkRunsOnceUnsupervisedEnds, noForkRunsOnceSupervisedEnds),
  nothingIsAddedOnceClosed.refines(nothingIsAddedOnceUnsupervisedEnds, nothingIsAddedOnceSupervisedEnds),
  aClosedHerdRefusesToStart.refines(noThreadIsStartedOnceUnsupervisedEnds, noThreadIsStartedOnceSupervisedEnds),
  unsupervisedRunsInTheScopeItMade.refines(unsupervisedClosesItsScopesHerd),
  supervisedRunsInTheScopeItMade.refines(supervisedClosesItsScopesHerd),
  aScopeEndsAfterItsHerdIsClosed.refines(unsupervisedClosesItsScopesHerd, supervisedClosesItsScopesHerd),
  aScopesHerdIsItsMakers.refines(unsupervisedClosesItsScopesHerd, supervisedClosesItsScopesHerd),
  aScopeGivesTheHerdItHolds.refines(aScopeEndsAfterItsHerdIsClosed),
  theCurrentScopeIsReadAndSet.refines(aScopeEndsAfterItsHerdIsClosed),
  aScopeHoldsTheHerdItIsMadeWith.refines(aScopesHerdIsItsMakers),

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
  closingsTraversalsReturn.refines(closingEndsOnceFoundEmpty),
  aTraversalThrowsOnlyWhatItsFunctionThrew.refines(closingsTraversalsReturn),
  closingTraversesWithAFunction.refines(closingsTraversalsReturn),
  closingsFunctionsReturn.refines(closingsTraversalsReturn),
  whatClosingsFunctionsApplyReturns.refines(closingsFunctionsReturn),
  closingKeepsItsVariableToItself.refines(closingsFunctionsReturn, whatClosingsFunctionsApplyInterrupts),
  closingsVariablesAreWrittenByItsFunctions.refines(whatClosingsFunctionsApplyInterrupts),
  joinThrowsOnlyAnInterruption.refines(closingsFunctionsReturn, whatClosingsFunctionsApplyReturns,
    whatClosingsFunctionsApplyInterrupts),
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
  theFlagStaysSet.refines(aClosedHerdRefusesToStart, closingSetsTheFlag),
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
  startThreadFirstSeesTheFlagUnset.refines(aClosedHerdRefusesToStart),

  // What a herd keeps to itself: its set.
  aHerdKeepsItsSetToItself.refines(aHerdsSetIsPlain, onlyStartThreadAddsToTheSet, onlyAForkFunctionRemoves),
  aKeySetHasOnlyItsMethods.refines(aHerdsSetIsPlain),
  whatAHerdsCodeCallsOfASet.refines(aHerdsSetIsPlain, onlyStartThreadAddsToTheSet, onlyAForkFunctionRemoves),
  theForkFunctionCallsFour.refines(whatAHerdsCodeCallsOfASet),

  startThreadReadsTheFlagUnset.refines(startThreadFirstSeesTheFlagUnset),
  getGivesTheFlag.refines(startThreadFirstSeesTheFlagUnset),
  closingSetsTheFlagItself.refines(closingSetsTheFlag), settingIsAtomic.refines(closingSetsTheFlag),
  setReturns.refines(closingEndsOnceFoundEmpty, closingSetsTheFlag),

  onlyStartThreadAddsToTheSet.refines(onlyStartThreadAdds, anAddedThreadHasNotBeenStarted,
    whoAddsIsCallingStartThread, aForkEndsOnceInterrupted),
  startThreadAddsWhileItRuns.refines(onlyStartThreadAdds, whoAddsIsCallingStartThread, aForkEndsOnceInterrupted),
  startThreadIsPendingWhileItAdds.refines(whoAddsIsCallingStartThread),
  anAddedThreadHasNotBeenStarted.refines(onlyStartThreadAdds),
  onlyItsMakerStartsAThread.refines(anAddedThreadHasNotBeenStarted),
  startThreadAddsWhatItsFactoryMade.refines(anAddedThreadHasNotBeenStarted, aForkEndsOnceInterrupted),
  startThreadAddsBeforeItStarts.refines(anAddedThreadHasNotBeenStarted),

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
    theWalkUpStaysOutOfHerds),

  // How a herd is made.
  herdsAreConstructed.refines(herdsAreMade, closingSetsTheFlag, aClosedHerdRefusesToStart, nothingIsAddedOnceEmpty,
    aForkEndsOnceInterrupted,
    nothingIsBeingAddedWhenEmpty, everyForkHasLeftOnceClosed, startThreadCallersStayInside, codeRunsBeforeLeaving),
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
    whatClosingsFunctionsApplyInterrupts),
  aHerdKeepsItsFields.refines(startThreadReadsTheFlagUnset, closingSetsTheFlagItself,
    theForkFunctionRemovesTheCurrentThread, closingEndsOnceFoundEmpty),
  currentThreadIsTheCaller.refines(closingSetsTheFlagItself, aForkRemovesOnlyItself, closingEndsOnceFoundEmpty,
    aScopesHerdIsItsMakers),

  addingIsAtomic.refines(liveForksAreInTheSet), anElementLeavesOnlyWhenRemoved.refines(liveForksAreInTheSet),
  aHerdsSetIsPlain.refines(liveForksAreInTheSet),

  // The execution is one of Ox's `ThreadHerd`, of its scopes, of `unsupervised` and of `supervised`, as its jar
  // has them.
  history.executing(Read.of(classOf[ThreadHerd], Set("ox/internal/ThreadHerd.tasty", "ox/OxError.tasty",
    "ox/unsupervised$package.tasty", "ox/supervised$package.tasty"))))
