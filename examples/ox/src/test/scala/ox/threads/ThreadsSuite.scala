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

  /** The claim that is not proven for a reason of its own, and the roots it is below: it has parts that do not
    * yet make it. Everything else is proven, or waits for it.
    */
  private val notProven = Map(
    "theTreeCheckStaysOutOfHerds" -> List("noForkRunsOnceClosed", "nothingIsAddedOnceClosed"))

  /** Each has parts: its step is what is not proven. */
  private val withParts = notProven.keySet

  /** What is assumed of the JDK, the JVM and Scala's objects: nothing of Ox, and nothing of who uses it. */
  private val ofThePlatform = Set("addingIsAtomic", "anElementLeavesOnlyWhenRemoved",
    "isEmptyFindsItEmptyUnlessAdded", "isEmptyReturns", "getGivesTheFlag", "settingIsAtomic",
    "aFlagBecomesOnlyWhatIsSet", "setReturns", "currentThreadIsTheCaller", "theJdkStaysOutOfHerds",
    "aThreadDoesOneThingAtATime", "aHerdKeepsItsFields",
    "aTraversalThrowsOnlyWhatItsFunctionThrew", "joinThrowsOnlyAnInterruption", "interruptReturns",
    "addSuppressedReturns", "herdsAreConstructed", "aHerdHoldsWhatItWasGiven",
    "anAtomicBooleanHasOnlyItsMethods", "aKeySetHasOnlyItsMethods")

  /** The root that is proven, and all it is proven from: the platform, and that a herd's flag is reached only
    * by the herd's own methods, which is assumed and not derived from the code.
    */
  private val provenRoot = "aClosedHerdRefusesToStart"
  private val theRootIsFrom = List("aFlagBecomesOnlyWhatIsSet", "aHerdHoldsWhatItWasGiven",
    "aHerdKeepsItsFields", "aHerdKeepsItsFlagToItself", "anAtomicBooleanHasOnlyItsMethods",
    "currentThreadIsTheCaller", "getGivesTheFlag", "herdsAreConstructed", "setReturns", "settingIsAtomic")

  /** The claims proven of Ox's code from that alone: no claim below them unproven, no other assumption. */
  private val provenOfTheCodeAlone = List("aForkFunctionRemovesAfterTheCode", "aHerdsFlagIsNew",
    "aHerdsMethodsOnlyGetAndSetAFlag", "aHerdsSetIsNew", "closingCallsFour", "closingSetsTheFlagItself",
    "theMembershipCheckCallsContains", "theOwnerCheckCallsCurrentThread", "theForkFunctionCallsFour",
    "whatAHerdsCodeCallsOfASet",
    "closingSetsTheFlagOnlyToTrue", "closingTraversesWithAFunction", "herdsAreMade",
    "startThreadAddsBeforeItStarts",
    "startThreadAddsWhatItsFactoryMade",
    "startThreadAddsWhileItRuns", "startThreadCallsFive", "startThreadFirstSeesTheFlagUnset",
    "startThreadIsPendingWhileItAdds", "startThreadReadsTheFlagUnset", "theClosingCheckCallsGet",
    "theClosingCheckStaysOutOfHerds", "theForkFunctionRemovesTheCurrentThread", "theTreeCheckCallsFour",
    "whatClosingsFunctionsApplyReturns")

  test("one root is proven; every step is, but one claim named here; what is above them waits".tag(Live)) {
    Ported.run(Projects.elaborated(oxThreads), Nil, Ported.proofs("ox", "OxThreads")).map { r =>
      val unproven = Ported.unproven(r)
      assertEquals(unproven.filter(_._2 != List("Check")), notProven.map((n, _) =>
        n -> (if withParts(n) then List("Check", "Parts") else List("Check", "OfCode"))),
        Ported.table(r))
      val below = notProven.values.flatten.toList.distinct.map(root =>
        root -> notProven.filter(_._2.contains(root)).keys.toList.sorted).toMap
      assertEquals(Ported.standsOn(r).map((root, on) => root -> on._1), below + (provenRoot -> Nil))
      assertEquals(Ported.standing(r)(provenRoot)._1.sorted, theRootIsFrom)
      assertEquals(Ported.standing(r).collect { case (n, (assumed, Nil)) if assumed.forall(ofThePlatform) => n }
        .toList.sorted, provenOfTheCodeAlone.sorted)
    }
  }
