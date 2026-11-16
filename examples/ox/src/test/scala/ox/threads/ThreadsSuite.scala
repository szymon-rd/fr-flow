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
    "whatTheChecksAskOfTheJdkStaysOutOfHerds", "aScopeHoldsWhatItWasGiven", "aScopeGivesTheHerdItHolds",
    "theCurrentScopeIsReadAndSet")

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
    "unsupervisedRunsInTheScopeItMade",
    "closingSetsTheFlagOnlyToTrue", "closingTraversesWithAFunction", "herdsAreMade",
    "startThreadAddsBeforeItStarts",
    "startThreadAddsWhatItsFactoryMade",
    "startThreadAddsWhileItRuns", "startThreadCallsFive", "startThreadFirstSeesTheFlagUnset",
    "startThreadIsPendingWhileItAdds", "startThreadReadsTheFlagUnset", "theClosingCheckCallsGet",
    "theClosingCheckStaysOutOfHerds", "theForkFunctionRemovesTheCurrentThread", "theTreeCheckCallsFour",
    "whatClosingsFunctionsApplyReturns")

  /** The claims about a scope that are not proven yet, each for a reason of its own: its step from its parts. */
  private val notProven = List("aScopeEndsAfterItsHerdIsClosed", "aScopesHerdIsItsMakers")

  /** What is said of a herd is all proven: the two roots on a herd, and the claim the scope's root is from. */
  private val ofAHerd = List("aClosedHerdRefusesToStart", "noForkRunsOnceClosed", "nothingIsAddedOnceClosed")

  test("what is said of a herd is proven; of a scope, the root waits for two claims named here".tag(Live)) {
    Ported.run(Projects.elaborated(oxThreads), Nil, Ported.proofs("ox", "OxThreads")).map { r =>
      assertEquals(Ported.unproven(r).filter(_._2 != List("Check")),
        notProven.map(_ -> List("Check", "Parts")).toMap, Ported.table(r))
      assertEquals(Ported.standsOn(r).map((root, on) => root -> on._1.sorted), Map(
        "aClosedHerdRefusesToStart" -> Nil, "nothingIsAddedOnceClosed" -> Nil,
        "noForkRunsOnceUnsupervisedEnds" -> notProven))
      ofAHerd.foreach(n => assertEquals(Ported.standing(r)(n)._2, Nil, n))
      assertEquals(Ported.standing(r)("aClosedHerdRefusesToStart")._1.sorted, theFlagRootIsFrom)
      val named = ofThePlatform ++ ofPrivateState ++ ofWhoUsesAHerd ++ ofScopesNotRead ++ suspectedFalse
      ofAHerd.foreach(n => assertEquals(Ported.standing(r)(n)._1.filterNot(named), Nil, n))
      List("noForkRunsOnceClosed", "nothingIsAddedOnceClosed").foreach(n =>
        assert(Ported.standing(r)(n)._1.contains("nothingIsAddedDuringTheLastCheck"), n))
      assertEquals(Ported.standing(r).collect { case (n, (assumed, Nil)) if assumed.forall(ofThePlatform) => n }
        .toList.sorted, provenOfTheCodeAlone.sorted)
    }
  }
