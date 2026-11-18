package ox.scopes

import frflow.*
import ox.live.*
import ox.threads.*

// The roots of the model of Ox's threads, and what is said of a scope. What each claim is from is said where it
// is stated (`.from`); these lists name the model's statements. The rest of the model, of a herd, is in
// `ox.threads` and in `ox.live`.

val roots: List[FrModel.Part] = List(
  noForkRunsOnceUnsupervisedEnds, nothingIsAddedOnceUnsupervisedEnds, noThreadIsStartedOnceUnsupervisedEnds,
  noForkRunsOnceSupervisedEnds, nothingIsAddedOnceSupervisedEnds, noThreadIsStartedOnceSupervisedEnds,
  whatAForkBeganIsOverOnceUnsupervisedEnds, whatAForkBeganIsOverOnceSupervisedEnds,
  forkUnsupervisedIsRefusedOnceUnsupervisedEnds, forkUnsupervisedIsRefusedOnceSupervisedEnds,
  forkIsRefusedOnceSupervisedEnds, forkUserIsRefusedOnceSupervisedEnds, forkCancellableIsRefusedOnceUnsupervisedEnds,
  forkCancellableIsRefusedOnceSupervisedEnds, unsupervisedClosesItsHerdInTime, aScopesHerdIsClosedInTime,
  unsupervisedComesToItsScope, whatUnsupervisedRunsEndsOnceItsCodeDoes, whatUnsupervisedRunsProceeds,
  makingAScopeReturnsInTime, unsupervisedProceeds, makingAScopeProceeds, makingAFlagReturnsInTime,
  makingASetReturnsInTime, makingAReferenceReturnsInTime, aScopeIsMadeInTime, closingCompletes,
  closingCompletesOnceItsHerdEmpties, aScopesClosingIsReached, runningInAScopeProceeds,
  whatRunningInAScopeAppliesProceeds, theCurrentScopeResponds, aScopesHerdResponds)

val ofScopes: List[FrModel.Part] = List(
  // A scope: `unsupervised` and `supervised` make one, run code in it, and its herd is closed before they end.
  unsupervisedClosesItsScopesHerd, supervisedClosesItsScopesHerd, forkUnsupervisedIsRefusedOnceClosed,
  forkUnsupervisedStartsAThread, forkCancellableIsRefusedOnceClosed, forkCancellableStartsAThread, forkStartsAThread,
  forkUserStartsAThread, aScopeMadeIsAnObject, forkErrorStartsAThread, forkUserErrorStartsAThread,
  asNoErrorModeKeepsTheHerd, aConstructedScopeIsMade, aScopeIsConstructed, aScopeKeepsItsFields,
  whatAForkBeganIsOverOnceClosed, noForkRunsOnceClosed, callsNest, aCallEndsAfterTheCallsItMade,
  nothingIsAddedOnceClosed, aClosedHerdRefusesToStart, unsupervisedRunsInTheScopeItMade,
  supervisedRunsInTheScopeItMade, aScopeEndsAfterItsHerdIsClosed, aScopesHerdIsItsMakers, aScopeGivesTheHerdItHolds,
  theCurrentScopeIsReadAndSet, aScopeHoldsTheHerdItIsMadeWith)
