package ox.threads

import frflow.*
import frflow.code.Read
import frflow.executions.*
import ox.internal.ThreadHerd

// The model of Ox's threads: what holds once a herd is closed (the roots), and what makes it hold. The first two
// roots rest on who starts a thread; the third, on the herd's flag alone, and on `ThreadHerd`'s code as Ox's jar
// has it.

val oxThreads: FrModel = FrModel("OxThreads")(
  noForkRunsOnceClosed, nothingIsAddedOnceClosed, aClosedHerdRefusesToStart,

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
  joinThrowsOnlyAnInterruption.refines(closingsFunctionsReturn, whatClosingsFunctionsApplyReturns),
  addSuppressedReturns.refines(closingsFunctionsReturn),
  interruptReturns.refines(whatClosingsFunctionsApplyReturns),
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
  closingCallsFour.refines(aHerdsMethodsOnlyGetAndSetAFlag),
  theOwnerCheckCallsCurrentThread.refines(aHerdsMethodsOnlyGetAndSetAFlag),
  theMembershipCheckCallsContains.refines(aHerdsMethodsOnlyGetAndSetAFlag),
  startThreadFirstSeesTheFlagUnset.refines(aClosedHerdRefusesToStart),

  startThreadReadsTheFlagUnset.refines(startThreadFirstSeesTheFlagUnset),
  getGivesTheFlag.refines(startThreadFirstSeesTheFlagUnset),
  closingSetsTheFlagItself.refines(closingSetsTheFlag), settingIsAtomic.refines(closingSetsTheFlag),
  setReturns.refines(closingEndsOnceFoundEmpty, closingSetsTheFlag),

  onlyStartThreadAddsToTheSet.refines(onlyStartThreadAdds, anAddedThreadHasNotBeenStarted,
    whoAddsIsCallingStartThread),
  startThreadAddsWhileItRuns.refines(onlyStartThreadAdds, whoAddsIsCallingStartThread),
  startThreadIsPendingWhileItAdds.refines(whoAddsIsCallingStartThread),
  anAddedThreadHasNotBeenStarted.refines(onlyStartThreadAdds),
  onlyItsMakerStartsAThread.refines(anAddedThreadHasNotBeenStarted),
  startThreadAddsWhatItsFactoryMade.refines(anAddedThreadHasNotBeenStarted),
  startThreadAddsBeforeItStarts.refines(anAddedThreadHasNotBeenStarted),

  onlyAForkFunctionRemoves.refines(aForkRemovesOnlyItself, codeRunsBeforeLeaving),
  theForkFunctionRemovesTheCurrentThread.refines(aForkRemovesOnlyItself),

  startThreadCallsFive.refines(startThreadStaysOutOfHerds, aHerdsMethodsOnlyGetAndSetAFlag),
  theClosingCheckStaysOutOfHerds.refines(startThreadStaysOutOfHerds),
  theTreeCheckStaysOutOfHerds.refines(startThreadStaysOutOfHerds),
  aFactoryStaysOutOfHerds.refines(startThreadStaysOutOfHerds),
  theClosingCheckCallsGet.refines(theClosingCheckStaysOutOfHerds, aHerdsMethodsOnlyGetAndSetAFlag),
  theTreeCheckCallsFour.refines(theTreeCheckStaysOutOfHerds, aHerdsMethodsOnlyGetAndSetAFlag),
  theJdkStaysOutOfHerds.refines(startThreadStaysOutOfHerds, theClosingCheckStaysOutOfHerds),
  aThreadDoesOneThingAtATime.refines(startThreadStaysOutOfHerds, theClosingCheckStaysOutOfHerds),

  // How a herd is made.
  herdsAreConstructed.refines(herdsAreMade, closingSetsTheFlag, aClosedHerdRefusesToStart),
  aHerdsFlagIsNew.refines(aHerdsFlagIsOnlyReadAndSet), aHerdsSetIsNew.refines(aHerdsSetIsPlain),
  aHerdHoldsWhatItWasGiven.refines(aHerdsFlagIsNew, aHerdsSetIsNew),

  herdsAreMade.refines(startThreadReadsTheFlagUnset, closingSetsTheFlagItself,
    theForkFunctionRemovesTheCurrentThread, startThreadAddsWhileItRuns, startThreadAddsWhatItsFactoryMade,
    startThreadAddsBeforeItStarts, closingEndsOnceFoundEmpty, closingSetsTheFlagOnlyToTrue,
    startThreadIsPendingWhileItAdds, nothingIsBeingAddedWhenEmpty, nothingIsAddedOnceEmpty,
    everyForkHasLeftOnceClosed,
    aForkFunctionRemovesAfterTheCode, startThreadCallsFive, theClosingCheckCallsGet, theTreeCheckCallsFour,
    closingTraversesWithAFunction, whatClosingsFunctionsApplyReturns, closingsFunctionsReturn,
    closingCallsFour, theOwnerCheckCallsCurrentThread, theMembershipCheckCallsContains),
  aHerdKeepsItsFields.refines(startThreadReadsTheFlagUnset, closingSetsTheFlagItself,
    theForkFunctionRemovesTheCurrentThread, closingEndsOnceFoundEmpty),
  currentThreadIsTheCaller.refines(closingSetsTheFlagItself, aForkRemovesOnlyItself, closingEndsOnceFoundEmpty),

  addingIsAtomic.refines(liveForksAreInTheSet), anElementLeavesOnlyWhenRemoved.refines(liveForksAreInTheSet),
  aHerdsSetIsPlain.refines(liveForksAreInTheSet),

  // The execution is one of Ox's `ThreadHerd`, as its jar has it.
  history.executing(Read.of(classOf[ThreadHerd], _ == "ox/internal/ThreadHerd.tasty")))
