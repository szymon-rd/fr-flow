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

  closingEndsOnEmpty.refines(everyForkHasLeftOnceClosed, nothingIsAddedOnceClosed),
  nothingIsAddedOnceEmpty.refines(everyForkHasLeftOnceClosed, nothingIsAddedOnceClosed),
  liveForksAreInTheSet.refines(everyForkHasLeftOnceClosed, nothingIsAddedOnceEmpty),

  startThreadCallersStayInside.refines(nothingIsAddedOnceEmpty),
  onlyStartThreadAdds.refines(nothingIsAddedOnceEmpty),

  startThreadIsCalledFromInside.refines(startThreadCallersStayInside),
  startThreadNeitherClosesNorLeaves.refines(startThreadCallersStayInside),
  aForkRemovesOnlyItself.refines(startThreadCallersStayInside),

  closingSetsTheFlag.refines(aClosedHerdRefusesToStart),
  theFlagStaysSet.refines(aClosedHerdRefusesToStart, closingSetsTheFlag),
  startThreadFirstSeesTheFlagUnset.refines(aClosedHerdRefusesToStart),

  startThreadReadsTheFlagUnset.refines(startThreadFirstSeesTheFlagUnset),
  getGivesTheFlag.refines(startThreadFirstSeesTheFlagUnset),
  closingSetsTheFlagItself.refines(closingSetsTheFlag), setMakesTheFlag.refines(closingSetsTheFlag),

  onlyStartThreadAddsToTheSet.refines(onlyStartThreadAdds, anAddedThreadHasNotBeenStarted),
  startThreadAddsWhileItRuns.refines(onlyStartThreadAdds),
  anAddedThreadHasNotBeenStarted.refines(onlyStartThreadAdds),
  onlyItsMakerStartsAThread.refines(anAddedThreadHasNotBeenStarted),
  startThreadAddsWhatItsFactoryMade.refines(anAddedThreadHasNotBeenStarted),
  startThreadAddsBeforeItStarts.refines(anAddedThreadHasNotBeenStarted),

  onlyAForkFunctionRemoves.refines(aForkRemovesOnlyItself),
  theForkFunctionRemovesTheCurrentThread.refines(aForkRemovesOnlyItself),

  herdsAreMade.refines(startThreadReadsTheFlagUnset, closingSetsTheFlagItself,
    theForkFunctionRemovesTheCurrentThread, startThreadAddsWhileItRuns, startThreadAddsWhatItsFactoryMade,
    startThreadAddsBeforeItStarts),
  aHerdKeepsItsFields.refines(startThreadReadsTheFlagUnset, closingSetsTheFlagItself,
    theForkFunctionRemovesTheCurrentThread),
  currentThreadIsTheCaller.refines(closingSetsTheFlagItself, aForkRemovesOnlyItself),

  nothingBeforeTheStart.refines(liveForksAreInTheSet), setCallsAreAtomic.refines(liveForksAreInTheSet),
  addPutsItIn.refines(liveForksAreInTheSet), removeTakesOnlyItOut.refines(liveForksAreInTheSet),
  onlyAddAndRemoveChangeASet.refines(liveForksAreInTheSet),

  // The execution is one of Ox's `ThreadHerd`, as its jar has it.
  history.executing(Read.of(classOf[ThreadHerd], _ == "ox/internal/ThreadHerd.tasty")))
