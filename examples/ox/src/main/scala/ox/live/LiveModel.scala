package ox.live

import frflow.*

// What happens in time, as the model has it. What each claim is from is said where it is stated (`.from`).

val inTime: List[FrModel.Part] = List(
  // What happens in time: closing's loop ends, once the herd's set rests empty.
  closingsTraversalsRespond, addingStopsOnceTheFlagIsSet, addingEndsOnceTheFlagIsSet, addingResponds,
  theOwnerCheckResponds, settingResponds, isEmptyResponds, isEmptyFindsARestingSetEmpty,

  // What happens in time: closing's traversals are responded to, and adding stops.
  closingsFunctionsRespond, aTraversalRespondsOnceItsFunctionDoes, aTraversalAppliesItsFunctionToElements,
  whatIsInAHerdsSetWasMadeToRun, anElementWasAdded, theExecutionBegins,

  // What happens in time: closing's functions are responded to.
  whatClosingsFunctionsApplyInterrupts, aForkEndsOnceInterrupted, joinRespondsOnceItsThreadHasRun,
  closingsFunctionsProceed, whatClosingsFunctionsApplyProceeds, interruptResponds, addSuppressedResponds,

  // What happens in time: a fork ends once interrupted.
  startThreadStartsWhatItAdded, aStartedThreadRunsItsFunction, aForkFunctionCompletesOnceItsCodeDoes,
  forkCodeCompletesOnceInterrupted, startThreadAddsOnce, aHerdsMethodsProceed, aForkFunctionProceeds,
  currentThreadResponds, removingResponds, discardResponds,
  // What happens in time: the herd's set empties, so closing completes.
  aHerdsSetEmptiesOnceTraversed, whatStaysInATraversedSetIsInterrupted, anInterruptedForkLeavesForGood,
  anElementEntersOnlyWhenAdded, aTraversalReachesWhatStays, closingsFunctionsInterrupt, aForkThatEndedStaysOut,
  aForkFunctionRemovesItsThread, currentThreadIsAnObject, removingTakesTheElementOut, aThreadActsOnlyOnceStarted,
  startThreadStartsAfterItsAddIsOver)
