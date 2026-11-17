package ox.scopes

import frflow.*
import ox.live.*
import ox.threads.*

// The roots of the model of Ox's threads, and what is said of a scope: each statement under what it helps
// prove. The rest of the model, of a herd, is in `ox.threads` and in `ox.live`.

val roots: List[FrModel.Part] = List(
  noForkRunsOnceUnsupervisedEnds, nothingIsAddedOnceUnsupervisedEnds, noThreadIsStartedOnceUnsupervisedEnds,
  noForkRunsOnceSupervisedEnds, nothingIsAddedOnceSupervisedEnds, noThreadIsStartedOnceSupervisedEnds,
  whatAForkBeganIsOverOnceUnsupervisedEnds, whatAForkBeganIsOverOnceSupervisedEnds,
  forkUnsupervisedIsRefusedOnceUnsupervisedEnds, forkUnsupervisedIsRefusedOnceSupervisedEnds,
  forkIsRefusedOnceSupervisedEnds, forkUserIsRefusedOnceSupervisedEnds,
  forkCancellableIsRefusedOnceUnsupervisedEnds, forkCancellableIsRefusedOnceSupervisedEnds,
  unsupervisedClosesItsHerdInTime, aScopesHerdIsClosedInTime.refines(unsupervisedClosesItsHerdInTime),
  unsupervisedComesToItsScope.refines(unsupervisedClosesItsHerdInTime),
  whatUnsupervisedRunsEndsOnceItsCodeDoes.refines(unsupervisedClosesItsHerdInTime),
  whatUnsupervisedRunsProceeds.refines(whatUnsupervisedRunsEndsOnceItsCodeDoes),
  makingAScopeReturnsInTime.refines(unsupervisedComesToItsScope),
  unsupervisedProceeds.refines(unsupervisedComesToItsScope),
  makingAScopeProceeds.refines(makingAScopeReturnsInTime),
  makingAFlagReturnsInTime.refines(makingAScopeReturnsInTime),
  makingASetReturnsInTime.refines(makingAScopeReturnsInTime),
  makingAReferenceReturnsInTime.refines(makingAScopeReturnsInTime),
  aScopeIsMadeInTime.refines(makingAScopeReturnsInTime),
  closingCompletes.refines(aScopesHerdIsClosedInTime),
  closingCompletesOnceItsHerdEmpties.refines(closingCompletes),
  aScopesClosingIsReached.refines(aScopesHerdIsClosedInTime),
  runningInAScopeProceeds.refines(aScopesClosingIsReached),
  whatRunningInAScopeAppliesProceeds.refines(aScopesClosingIsReached),
  theCurrentScopeResponds.refines(aScopesClosingIsReached, unsupervisedComesToItsScope),
  aScopesHerdResponds.refines(aScopesClosingIsReached))

val ofScopes: List[FrModel.Part] = List(
  // A scope: `unsupervised` and `supervised` make one, run code in it, and its herd is closed before they end.
  unsupervisedClosesItsScopesHerd.refines(noForkRunsOnceUnsupervisedEnds, nothingIsAddedOnceUnsupervisedEnds,
    noThreadIsStartedOnceUnsupervisedEnds, whatAForkBeganIsOverOnceUnsupervisedEnds,
    forkUnsupervisedIsRefusedOnceUnsupervisedEnds, forkCancellableIsRefusedOnceUnsupervisedEnds),
  supervisedClosesItsScopesHerd.refines(noForkRunsOnceSupervisedEnds, nothingIsAddedOnceSupervisedEnds,
    noThreadIsStartedOnceSupervisedEnds, whatAForkBeganIsOverOnceSupervisedEnds,
    forkUnsupervisedIsRefusedOnceSupervisedEnds, forkIsRefusedOnceSupervisedEnds,
    forkUserIsRefusedOnceSupervisedEnds, forkCancellableIsRefusedOnceSupervisedEnds),
  forkUnsupervisedIsRefusedOnceClosed.refines(forkUnsupervisedIsRefusedOnceUnsupervisedEnds,
    forkUnsupervisedIsRefusedOnceSupervisedEnds),
  forkUnsupervisedStartsAThread.refines(forkUnsupervisedIsRefusedOnceClosed),
  forkCancellableIsRefusedOnceClosed.refines(forkCancellableIsRefusedOnceUnsupervisedEnds,
    forkCancellableIsRefusedOnceSupervisedEnds),
  forkCancellableStartsAThread.refines(forkCancellableIsRefusedOnceClosed),
  forkStartsAThread.refines(forkIsRefusedOnceSupervisedEnds),
  forkUserStartsAThread.refines(forkUserIsRefusedOnceSupervisedEnds),
  aScopeMadeIsAnObject.refines(forkIsRefusedOnceSupervisedEnds, forkUserIsRefusedOnceSupervisedEnds),
  forkErrorStartsAThread.refines(forkStartsAThread), forkUserErrorStartsAThread.refines(forkUserStartsAThread),
  asNoErrorModeKeepsTheHerd.refines(forkStartsAThread, forkUserStartsAThread),
  aConstructedScopeIsMade.refines(aScopeMadeIsAnObject, asNoErrorModeKeepsTheHerd),
  aScopeIsConstructed.refines(aScopeMadeIsAnObject, asNoErrorModeKeepsTheHerd),
  aScopeKeepsItsFields.refines(asNoErrorModeKeepsTheHerd, forkErrorStartsAThread, forkUserErrorStartsAThread),
  whatAForkBeganIsOverOnceClosed.refines(whatAForkBeganIsOverOnceUnsupervisedEnds,
    whatAForkBeganIsOverOnceSupervisedEnds),
  noForkRunsOnceClosed.refines(noForkRunsOnceUnsupervisedEnds, noForkRunsOnceSupervisedEnds,
    whatAForkBeganIsOverOnceClosed),
  callsNest.refines(whatAForkBeganIsOverOnceClosed), aCallEndsAfterTheCallsItMade.refines(callsNest),
  nothingIsAddedOnceClosed.refines(nothingIsAddedOnceUnsupervisedEnds, nothingIsAddedOnceSupervisedEnds),
  aClosedHerdRefusesToStart.refines(noThreadIsStartedOnceUnsupervisedEnds, noThreadIsStartedOnceSupervisedEnds,
    forkUnsupervisedIsRefusedOnceClosed, forkIsRefusedOnceSupervisedEnds, forkCancellableIsRefusedOnceClosed,
    forkUserIsRefusedOnceSupervisedEnds),
  unsupervisedRunsInTheScopeItMade.refines(unsupervisedClosesItsScopesHerd),
  supervisedRunsInTheScopeItMade.refines(supervisedClosesItsScopesHerd),
  aScopeEndsAfterItsHerdIsClosed.refines(unsupervisedClosesItsScopesHerd, supervisedClosesItsScopesHerd),
  aScopesHerdIsItsMakers.refines(unsupervisedClosesItsScopesHerd, supervisedClosesItsScopesHerd,
    aScopesHerdIsClosedInTime),
  aScopeGivesTheHerdItHolds.refines(aScopeEndsAfterItsHerdIsClosed, aScopesClosingIsReached,
    forkUnsupervisedStartsAThread, forkCancellableStartsAThread),
  theCurrentScopeIsReadAndSet.refines(aScopeEndsAfterItsHerdIsClosed, aScopesClosingIsReached,
    unsupervisedComesToItsScope),
  aScopeHoldsTheHerdItIsMadeWith.refines(aScopesHerdIsItsMakers, asNoErrorModeKeepsTheHerd))
