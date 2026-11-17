package ox.threads

import frflow.project.{Live, Ported, Projects}
import java.nio.file.{Files, Paths}
import scala.annotation.experimental
import scala.concurrent.duration.*

/** The model of Ox's threads: FrFlow generates its Rocq, and each step from parts to a claim is proven by hand in
  * the claim's proof file (`examples/ox/rocq/Proofs/OxThreads`). What is not proven is named here.
  */
@experimental class ThreadsSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 60.minutes

  // The Rocq is written out as a check has it, with what each proof file is asked: to compile a proof by hand.
  test("the model elaborates, its calls named as Ox's code names them") {
    val files = Projects.provingNamed(Projects.elaborated(oxThreads), Ported.proofs("ox", "OxThreads")).rocq.files
    files.foreach { (file, text) =>
      val p = Paths.get("examples/ox/target/generated/threads").resolve(file.toString)
      Files.createDirectories(p.getParent)
      Files.writeString(p, text)
    }
    val text = files.map(_._2).mkString("\n")
    assert(text.contains("\"ox.internal.ThreadHerd startThread scala.Function0:scala.Unit\""), "startThread")
    assert(text.contains("(heldIn \"ox.internal.ThreadHerd threads\"%string h)"), "threads")
  }

  /** What is assumed of the JDK, the JVM and Scala's objects: nothing of Ox, and nothing of who uses it. */
  private val ofThePlatform = Set("addingIsAtomic", "anElementLeavesOnlyWhenRemoved",
    "isEmptyFindsItEmptyUnlessAdded", "isEmptyReturns", "getGivesTheFlag", "settingIsAtomic",
    "aFlagBecomesOnlyWhatIsSet", "setReturns", "currentThreadIsTheCaller", "theJdkStaysOutOfHerds",
    "aThreadDoesOneThingAtATime", "aHerdKeepsItsFields",
    "aTraversalThrowsOnlyWhatItsFunctionThrew", "joinThrowsOnlyAnInterruption", "interruptReturns",
    "addSuppressedReturns", "herdsAreConstructed", "aHerdHoldsWhatItWasGiven",
    "anAtomicBooleanHasOnlyItsMethods", "aKeySetHasOnlyItsMethods",
    "whatTheChecksAskOfTheJdkStaysOutOfHerds", "aScopeHoldsTheHerdItIsMadeWith", "aScopeGivesTheHerdItHolds",
    "theCurrentScopeIsReadAndSet", "aTraversalAppliesItsFunctionToElements", "anElementWasAdded",
    "isEmptyFindsARestingSetEmpty", "anElementEntersOnlyWhenAdded", "aTraversalReachesWhatStays",
    "removingTakesTheElementOut", "aThreadActsOnlyOnceStarted", "currentThreadIsAnObject",
    "aCallEndsAfterTheCallsItMade", "aScopeIsConstructed", "aScopeKeepsItsFields",
    "aHerdsValsAreAssignedWhereItIsMade", "aScopesValsAreAssignedWhereItIsMade")

  /** What is assumed to happen in time: of who schedules threads (a call of code that waits for nothing makes its
    * next event), of the JDK and of the thread factory (a call is responded to; a started thread runs).
    */
  private val ofWhatHappensInTime = Set("aHerdsMethodsProceed", "aForkFunctionProceeds", "currentThreadResponds",
    "removingResponds", "discardResponds", "aStartedThreadRunsItsFunction", "closingsFunctionsProceed",
    "whatClosingsFunctionsApplyProceeds", "interruptResponds", "addSuppressedResponds",
    "joinRespondsOnceItsThreadHasRun", "aTraversalRespondsOnceItsFunctionDoes", "theExecutionBegins",
    "settingResponds", "isEmptyResponds", "addingResponds", "runningInAScopeProceeds",
    "whatRunningInAScopeAppliesProceeds", "theCurrentScopeResponds", "aScopesHerdResponds",
    "unsupervisedProceeds", "makingAScopeProceeds", "whatUnsupervisedRunsProceeds", "makingAFlagReturnsInTime",
    "makingASetReturnsInTime", "makingAReferenceReturnsInTime", "aScopeIsMadeInTime")

  /** What is assumed of the code a fork is given: a restriction on who uses Ox. */
  private val ofForkCode = List("forkCodeCompletesOnceInterrupted")

  /** What is assumed beside the platform, by what it is about: each named in the README. */
  private val ofPrivateState = List("aHerdKeepsItsFlagToItself", "aHerdKeepsItsSetToItself",
    "closingKeepsItsVariableToItself", "closingsVariablesAreWrittenByItsFunctions", "onlyItsMakerStartsAThread",
    "onlyAForkFunctionCallsTheCode", "aHerdsValsAreReadByItsCode", "aScopesValsAreReadOnceItIsConstructed")
  private val ofWhoUsesAHerd = List("startThreadIsCalledFromInside", "aThreadRunsOneForkFunctionOnce",
    "aFactoryStaysOutOfHerds")
  private val ofScopesNotRead = List("aScopesHerdAndParentStayOutOfHerds")
  /** False of Ox 1.1.0 (a defect that can be reproduced); assumed until the patched code is what is read. */
  private val falseOfOx110 = List("nothingIsAddedDuringTheLastCheck")

  /** The root on the flag is proven from the platform and one assumption about the herd's private flag. */
  private val theFlagRootIsFrom = List("aFlagBecomesOnlyWhatIsSet", "aHerdHoldsWhatItWasGiven",
    "aHerdKeepsItsFields", "aHerdKeepsItsFlagToItself", "aScopeHoldsTheHerdItIsMadeWith",
    "anAtomicBooleanHasOnlyItsMethods",
    "currentThreadIsTheCaller", "getGivesTheFlag", "herdsAreConstructed", "setReturns", "settingIsAtomic")

  /** The claims proven of Ox's code from that alone: no claim below them unproven, no other assumption. */
  private val provenOfTheCodeAlone = List("aForkFunctionRemovesAfterTheCode", "aHerdsFlagIsNew",
    "aHerdsMethodsOnlyGetAndSetAFlag", "aHerdsSetIsNew", "closingCallsFour", "closingSetsTheFlagItself",
    "theMembershipCheckCallsContains", "theOwnerCheckCallsCurrentThread", "theForkFunctionCallsFour",
    "whatAHerdsCodeCallsOfASet", "theWalkUpCallsFour", "theMembershipCheckStaysOutOfHerds",
    "unsupervisedRunsInTheScopeItMade", "supervisedRunsInTheScopeItMade", "aScopeEndsAfterItsHerdIsClosed",
    "aScopesHerdIsItsMakers", "unsupervisedClosesItsScopesHerd", "supervisedClosesItsScopesHerd",
    "startThreadAddsOnce",
    "closingSetsTheFlagOnlyToTrue", "closingTraversesWithAFunction", "herdsAreMade",
    "startThreadAddsBeforeItStarts",
    "startThreadAddsWhatItsFactoryMade",
    "startThreadAddsWhileItRuns", "startThreadCallsFive", "startThreadFirstSeesTheFlagUnset",
    "startThreadIsPendingWhileItAdds", "startThreadReadsTheFlagUnset", "theClosingCheckCallsGet",
    "theClosingCheckStaysOutOfHerds", "theForkFunctionRemovesTheCurrentThread", "theTreeCheckCallsFour",
    "whatClosingsFunctionsApplyReturns", "startThreadStartsAfterItsAddIsOver", "aForkFunctionRemovesItsThread",
    "callsNest", "forkUnsupervisedStartsAThread", "aConstructedScopeIsMade", "aScopeMadeIsAnObject",
    "asNoErrorModeKeepsTheHerd", "forkErrorStartsAThread", "forkStartsAThread", "forkCancellableStartsAThread",
    "forkUserErrorStartsAThread", "forkUserStartsAThread", "aReadyHerdsValsAreWritten",
    "aConstructedScopesValsAreWritten")

  /** What holds once a call of `unsupervised`, or of `supervised`, has completed. */
  private val safe = List("Unsupervised", "Supervised").flatMap(of =>
    List(s"noForkRunsOnce${of}Ends", s"nothingIsAddedOnce${of}Ends", s"noThreadIsStartedOnce${of}Ends",
      s"whatAForkBeganIsOverOnce${of}Ends", s"forkUnsupervisedIsRefusedOnce${of}Ends",
      s"forkCancellableIsRefusedOnce${of}Ends")) ++
    List("forkIsRefusedOnceSupervisedEnds", "forkUserIsRefusedOnceSupervisedEnds")

  /** What happens in time. */
  private val live = List("unsupervisedClosesItsHerdInTime")

  /** That what Ox's code writes plainly has no data race, with what each is from. */
  private val unraced = Map(
    "noRaceOnAHerdsVals" -> List("aHerdsValsAreAssignedWhereItIsMade", "aHerdsValsAreReadByItsCode",
      "aScopeHoldsTheHerdItIsMadeWith", "herdsAreConstructed"),
    "noRaceOnClosingsVariables" -> List("aScopeHoldsTheHerdItIsMadeWith", "closingKeepsItsVariableToItself",
      "herdsAreConstructed"),
    "noRaceOnAScopesVals" -> List("aScopesValsAreAssignedWhereItIsMade", "aScopesValsAreReadOnceItIsConstructed"))
  private val roots = safe ++ live ++ unraced.keys

  /** What rests on the herd's flag alone: that no thread is started, and so that a fork is refused. */
  private val onTheFlag = safe.filter(n => n.startsWith("noThreadIsStarted") || n.startsWith("fork"))

  /** What rests on the assumption false of Ox 1.1.0: everything else. */
  private val onTheLastCheck = safe.filterNot(onTheFlag.contains) ++
    List("noForkRunsOnceClosed", "nothingIsAddedOnceClosed", "whatAForkBeganIsOverOnceClosed")

  test("every root is proven: no claim is unproven, and what each root is from is of the kinds named".tag(Live)) {
    Ported.run(Projects.elaborated(oxThreads), Nil, Ported.proofs("ox", "OxThreads")).map { r =>
      assertEquals(Ported.unproven(r), Map.empty[String, List[String]], Ported.table(r))
      assertEquals(Ported.standsOn(r).map((root, on) => root -> on._1), roots.map(_ -> Nil).toMap)
      val standing = Ported.standing(r)
      assertEquals(standing("aClosedHerdRefusesToStart")._1.sorted, theFlagRootIsFrom)
      val named = ofThePlatform ++ ofPrivateState ++ ofWhoUsesAHerd ++ ofScopesNotRead ++ falseOfOx110
      safe.foreach(root => assertEquals(standing(root)._1.filterNot(named), Nil, root))
      // what happens in time rests on nothing false of Ox 1.1.0, and on the code a fork is given ending
      live.foreach { root =>
        val on = standing(root)._1
        assertEquals(on.filterNot(named ++ ofWhatHappensInTime ++ ofForkCode), Nil, root)
        assert(ofForkCode.forall(on.contains) && !on.contains("nothingIsAddedDuringTheLastCheck"), root)
      }
      // that there is no data race rests on who reads and who writes a field, and on no value read
      unraced.foreach((root, from) => assertEquals(standing(root)._1.sorted, from, root))
      // that adding stops rests on neither
      val adding = standing("addingStopsOnceTheFlagIsSet")._1
      assert(!adding.exists(a => ofForkCode.contains(a) || a == "nothingIsAddedDuringTheLastCheck"), adding)
      // that no thread is started rests on the platform and on the herd's flag being its own, and no more
      onTheFlag.foreach(root => assertEquals(
        standing(root)._1.filterNot(ofThePlatform), List("aHerdKeepsItsFlagToItself"), root))
      onTheLastCheck.foreach(n =>
        assert(standing(n)._1.contains("nothingIsAddedDuringTheLastCheck"), n))
      assertEquals(standing.collect { case (n, (assumed, Nil)) if assumed.forall(ofThePlatform) => n }
        .toList.sorted, provenOfTheCodeAlone.sorted)
    }
  }
