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
    "whatTheChecksAskOfTheJdkStaysOutOfHerds")

  /** What is assumed beside the platform, by what it is about: each named in the README. */
  private val ofPrivateState = List("aHerdKeepsItsFlagToItself", "aHerdKeepsItsSetToItself",
    "closingKeepsItsVariableToItself", "onlyItsMakerStartsAThread", "onlyAForkFunctionCallsTheCode")
  private val ofWhoUsesAHerd = List("startThreadIsCalledFromInside", "aThreadRunsOneForkFunctionOnce",
    "aFactoryStaysOutOfHerds")
  private val ofScopesNotRead = List("aScopesHerdAndParentStayOutOfHerds")
  private val suspectedFalse = List("nothingIsAddedDuringTheLastCheck")

  /** The root on the flag is proven from the platform and one assumption about the herd's private flag. */
  private val theFlagRootIsFrom = List("aFlagBecomesOnlyWhatIsSet", "aHerdHoldsWhatItWasGiven",
    "aHerdKeepsItsFields", "aHerdKeepsItsFlagToItself", "anAtomicBooleanHasOnlyItsMethods",
    "currentThreadIsTheCaller", "getGivesTheFlag", "herdsAreConstructed", "setReturns", "settingIsAtomic")

  /** The claims proven of Ox's code from that alone: no claim below them unproven, no other assumption. */
  private val provenOfTheCodeAlone = List("aForkFunctionRemovesAfterTheCode", "aHerdsFlagIsNew",
    "aHerdsMethodsOnlyGetAndSetAFlag", "aHerdsSetIsNew", "closingCallsFour", "closingSetsTheFlagItself",
    "theMembershipCheckCallsContains", "theOwnerCheckCallsCurrentThread", "theForkFunctionCallsFour",
    "whatAHerdsCodeCallsOfASet", "theWalkUpCallsFour", "theMembershipCheckStaysOutOfHerds",
    "closingSetsTheFlagOnlyToTrue", "closingTraversesWithAFunction", "herdsAreMade",
    "startThreadAddsBeforeItStarts",
    "startThreadAddsWhatItsFactoryMade",
    "startThreadAddsWhileItRuns", "startThreadCallsFive", "startThreadFirstSeesTheFlagUnset",
    "startThreadIsPendingWhileItAdds", "startThreadReadsTheFlagUnset", "theClosingCheckCallsGet",
    "theClosingCheckStaysOutOfHerds", "theForkFunctionRemovesTheCurrentThread", "theTreeCheckCallsFour",
    "whatClosingsFunctionsApplyReturns")

  private val roots = List("aClosedHerdRefusesToStart", "noForkRunsOnceClosed", "nothingIsAddedOnceClosed")

  test("every root is proven: no claim is unproven, and what each root is from is of the kinds named".tag(Live)) {
    Ported.run(Projects.elaborated(oxThreads), Nil, Ported.proofs("ox", "OxThreads")).map { r =>
      assertEquals(Ported.unproven(r), Map.empty[String, List[String]], Ported.table(r))
      assertEquals(Ported.standsOn(r).map((root, on) => root -> on._1), roots.map(_ -> Nil).toMap)
      assertEquals(Ported.standing(r)("aClosedHerdRefusesToStart")._1.sorted, theFlagRootIsFrom)
      val named = ofThePlatform ++ ofPrivateState ++ ofWhoUsesAHerd ++ ofScopesNotRead ++ suspectedFalse
      roots.foreach(root => assertEquals(Ported.standing(r)(root)._1.filterNot(named), Nil, root))
      List("noForkRunsOnceClosed", "nothingIsAddedOnceClosed").foreach(root =>
        assert(Ported.standing(r)(root)._1.contains("nothingIsAddedDuringTheLastCheck"), root))
      assertEquals(Ported.standing(r).collect { case (n, (assumed, Nil)) if assumed.forall(ofThePlatform) => n }
        .toList.sorted, provenOfTheCodeAlone.sorted)
    }
  }
