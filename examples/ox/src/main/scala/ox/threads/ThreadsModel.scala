package ox.threads

import frflow.*

// The model of Ox's threads: what holds once a herd is closed (the roots), and what makes it hold. The first two
// roots rest on who starts a thread; the third, on the herd's flag alone.

val oxThreads: FrModel = FrModel("OxThreads")(
  noForkRunsOnceClosed, nothingIsAddedOnceClosed, aClosedHerdRefusesToStart,

  everyForkHasLeftOnceClosed.refines(noForkRunsOnceClosed),
  codeRunsBeforeLeaving.refines(noForkRunsOnceClosed),

  closingEndsOnEmpty.refines(everyForkHasLeftOnceClosed, nothingIsAddedOnceClosed),
  nothingIsAddedOnceEmpty.refines(everyForkHasLeftOnceClosed, nothingIsAddedOnceClosed),
  liveForksAreInTheSet.refines(everyForkHasLeftOnceClosed, nothingIsAddedOnceEmpty),

  startThreadCallersStayInside.refines(nothingIsAddedOnceEmpty),
  onlyStartThreadAdds.refines(nothingIsAddedOnceEmpty),

  startThreadIsCalledFromInside.refines(startThreadCallersStayInside),
  startThreadNeitherClosesNorLeaves.refines(startThreadCallersStayInside),
  aForkRemovesOnlyItself.refines(startThreadCallersStayInside),

  closingSetsTheFlag.refines(aClosedHerdRefusesToStart), theFlagStaysSet.refines(aClosedHerdRefusesToStart),
  startThreadFirstSeesTheFlagUnset.refines(aClosedHerdRefusesToStart),
  aCallCompletesAfterItIsMade.refines(aClosedHerdRefusesToStart),

  nothingBeforeTheStart.refines(liveForksAreInTheSet), setCallsAreAtomic.refines(liveForksAreInTheSet),
  addPutsItIn.refines(liveForksAreInTheSet), removeTakesOnlyItOut.refines(liveForksAreInTheSet),
  onlyAddAndRemoveChangeASet.refines(liveForksAreInTheSet))
