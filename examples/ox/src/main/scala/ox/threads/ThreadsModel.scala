package ox.threads

import frflow.*

// The model of Ox's threads: what holds once a herd is closed (the roots), and what makes it hold.

val oxThreads: FrModel = FrModel("OxThreads")(
  noForkRunsOnceClosed, nothingIsAddedOnceClosed,

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

  nothingBeforeTheStart.refines(liveForksAreInTheSet), setCallsAreAtomic.refines(liveForksAreInTheSet),
  addPutsItIn.refines(liveForksAreInTheSet), removeTakesOnlyItOut.refines(liveForksAreInTheSet),
  onlyAddAndRemoveChangeASet.refines(liveForksAreInTheSet))
