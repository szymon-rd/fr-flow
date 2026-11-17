package ox.live

import frflow.*
import ox.scopes.makingAScopeReturnsInTime

// What happens in time, as the model has it: each statement under what it helps prove.

val inTime: List[FrModel.Part] = List(
  // What happens in time: closing's loop ends, once the herd's set rests empty.
  closingsTraversalsRespond.refines(closingCompletesOnceItsHerdEmpties),
  addingStopsOnceTheFlagIsSet.refines(closingCompletesOnceItsHerdEmpties, addingEndsOnceTheFlagIsSet),
  addingEndsOnceTheFlagIsSet.refines(closingCompletesOnceItsHerdEmpties),
  addingResponds.refines(addingEndsOnceTheFlagIsSet), theOwnerCheckResponds.refines(closingCompletesOnceItsHerdEmpties),
  settingResponds.refines(closingCompletesOnceItsHerdEmpties),
  isEmptyResponds.refines(closingCompletesOnceItsHerdEmpties),
  isEmptyFindsARestingSetEmpty.refines(closingCompletesOnceItsHerdEmpties),

  // What happens in time: closing's traversals are responded to, and adding stops.
  closingsFunctionsRespond.refines(closingsTraversalsRespond, whatStaysInATraversedSetIsInterrupted),
  aTraversalRespondsOnceItsFunctionDoes.refines(closingsTraversalsRespond),
  aTraversalAppliesItsFunctionToElements.refines(closingsTraversalsRespond),
  whatIsInAHerdsSetWasMadeToRun.refines(closingsTraversalsRespond, whatStaysInATraversedSetIsInterrupted,
    aHerdsSetEmptiesOnceTraversed),
  anElementWasAdded.refines(whatIsInAHerdsSetWasMadeToRun, aHerdsSetEmptiesOnceTraversed),
  theExecutionBegins.refines(addingStopsOnceTheFlagIsSet, addingEndsOnceTheFlagIsSet,
    aHerdsSetEmptiesOnceTraversed),

  // What happens in time: closing's functions are responded to.
  whatClosingsFunctionsApplyInterrupts.refines(closingsFunctionsRespond, closingsFunctionsInterrupt),
  aForkEndsOnceInterrupted.refines(closingsFunctionsRespond),
  joinRespondsOnceItsThreadHasRun.refines(closingsFunctionsRespond),
  closingsFunctionsProceed.refines(closingsFunctionsRespond),
  whatClosingsFunctionsApplyProceeds.refines(closingsFunctionsRespond),
  interruptResponds.refines(closingsFunctionsRespond),
  addSuppressedResponds.refines(closingsFunctionsRespond),

  // What happens in time: a fork ends once interrupted.
  startThreadStartsWhatItAdded.refines(aForkEndsOnceInterrupted, anInterruptedForkLeavesForGood),
  aStartedThreadRunsItsFunction.refines(aForkEndsOnceInterrupted, anInterruptedForkLeavesForGood),
  aForkFunctionCompletesOnceItsCodeDoes.refines(aForkEndsOnceInterrupted, anInterruptedForkLeavesForGood),
  forkCodeCompletesOnceInterrupted.refines(aForkEndsOnceInterrupted, anInterruptedForkLeavesForGood),
  startThreadAddsOnce.refines(startThreadStartsWhatItAdded, addingStopsOnceTheFlagIsSet),
  aHerdsMethodsProceed.refines(startThreadStartsWhatItAdded, theOwnerCheckResponds,
    closingCompletesOnceItsHerdEmpties),
  aForkFunctionProceeds.refines(aForkFunctionCompletesOnceItsCodeDoes),
  currentThreadResponds.refines(aForkFunctionCompletesOnceItsCodeDoes, theOwnerCheckResponds,
    makingAScopeReturnsInTime),
  removingResponds.refines(aForkFunctionCompletesOnceItsCodeDoes, aHerdsSetEmptiesOnceTraversed),
  discardResponds.refines(aForkFunctionCompletesOnceItsCodeDoes),
  // What happens in time: the herd's set empties, so closing completes.
  aHerdsSetEmptiesOnceTraversed.refines(closingCompletes),
  whatStaysInATraversedSetIsInterrupted.refines(aHerdsSetEmptiesOnceTraversed),
  anInterruptedForkLeavesForGood.refines(aHerdsSetEmptiesOnceTraversed),
  anElementEntersOnlyWhenAdded.refines(whatStaysInATraversedSetIsInterrupted, aForkThatEndedStaysOut),
  aTraversalReachesWhatStays.refines(whatStaysInATraversedSetIsInterrupted),
  closingsFunctionsInterrupt.refines(whatStaysInATraversedSetIsInterrupted),
  aForkThatEndedStaysOut.refines(anInterruptedForkLeavesForGood),
  aForkFunctionRemovesItsThread.refines(aForkThatEndedStaysOut),
  currentThreadIsAnObject.refines(aForkThatEndedStaysOut),
  removingTakesTheElementOut.refines(aForkThatEndedStaysOut),
  aThreadActsOnlyOnceStarted.refines(aForkThatEndedStaysOut),
  startThreadStartsAfterItsAddIsOver.refines(aForkThatEndedStaysOut))
