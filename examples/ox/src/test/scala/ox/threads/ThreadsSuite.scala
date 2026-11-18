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

  /** The model's assumptions of the kinds named: each says what it is about where it is stated (`About`). */
  private def about(kinds: String*): Set[String] =
    oxThreads.nodes.filter(_.head.about.exists(kinds.contains)).map(_.head.id.value).toSet

  /** What is assumed of the JDK, the JVM and Scala's objects: nothing of Ox, and nothing of who uses it. */
  private val ofThePlatform = about(About.jdk, About.objects)

  /** What is assumed to happen in time: of who schedules threads (a call of code that waits for nothing makes its
    * next event), of the JDK and of the thread factory (a call is responded to; a started thread runs).
    */
  private val ofWhatHappensInTime = about(About.time)

  /** What is assumed of the code a fork is given: a restriction on who uses Ox. */
  private val ofForkCode = about(About.forkCode)

  /** What is assumed beside the platform, by what it is about. */
  private val ofPrivateState = about(About.privateField, About.readers, About.variables, About.reach)
  private val ofWhoUsesAHerd = about(About.use, About.factory)
  private val ofScopesNotRead = about(About.scopes)
  /** False of Ox 1.1.0 (a defect that can be reproduced); assumed until the patched code is what is read. */
  private val falseOfOx110 = about(About.falseOfOx)

  /** The README's list of what is assumed, as the model has it: each kind with its assumptions. */
  private def listed: String = About.all.map { kind =>
    val names = oxThreads.nodes.filter(_.head.about.contains(kind)).map(_.head.id.value).distinct
    val words = s"- **$kind** (${names.size}):" :: names.init.map(n => s"`$n`,") ::: List(s"`${names.last}`.")
    words.tail.foldLeft(List(words.head))((lines, w) =>
      if lines.head.length + 1 + w.length <= 118 then (lines.head + " " + w) :: lines.tail else ("  " + w) :: lines)
      .reverse.mkString("\n")
  }.mkString("\n")

  test("each assumption says what it is about; the README lists them by it, and JDK.md leaves out none of the JDK's") {
    val assumed = Ported.assumptions(Projects.elaborated(oxThreads))
    assertEquals(about(About.all*), assumed)
    assertEquals(oxThreads.nodes.flatMap(_.head.about).toSet -- About.all, Set.empty[String])
    val readme = Projects.base.resolve("examples/ox/README.md")
    val (text, begin, end) =
      (Files.readString(readme), "<!-- assumed: written from the model by ThreadsSuite -->", "<!-- /assumed -->")
    val written = text.take(text.indexOf(begin) + begin.length) + "\n" + listed + "\n" + text.drop(text.indexOf(end))
    if sys.env.contains("FRFLOW_ROCQ_WRITE") then Files.writeString(readme, written): Unit
    assertEquals(Files.readString(readme), written)
    val jdk = Files.readString(Projects.base.resolve("examples/ox/JDK.md"))
    assertEquals(about(About.jdk).filterNot(n => jdk.contains(s"`$n`")), Set.empty[String])
    // what the census of the kernel's JDK members names as assumed is assumed here
    val census = Files.readString(Projects.base.resolve("examples/ox/rocq/Ox/Tree/Assumed.v"))
    val named = "Stateful \\[([^\\]]*)\\]".r.findAllMatchIn(census).flatMap(m =>
      "\"([A-Za-z0-9]+)\"".r.findAllMatchIn(m.group(1)).map(_.group(1))).toSet
    assertEquals(named -- assumed, Set.empty[String])
  }

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

  /** The model checked, with what each node stands on: run once, by the first test that asks. */
  private lazy val checked = Ported.run(Projects.elaborated(oxThreads), Nil, Ported.proofs("ox", "OxThreads"))
    .map(r => (r, Ported.standing(r).view.mapValues(_._1).toMap)).memoize.unsafeRunSync()

  test("every root is proven, and no claim is unproven".tag(Live)) {
    checked.map { (r, _) =>
      assertEquals(Ported.unproven(r), Map.empty[String, List[String]], Ported.table(r))
      assertEquals(Ported.standsOn(r).map((root, on) => root -> on._1), roots.map(_ -> Nil).toMap)
    }
  }

  /** What safety may rest on: every kind but what happens in time and what the code a fork is given does. */
  private val named = ofThePlatform ++ ofPrivateState ++ ofWhoUsesAHerd ++ ofScopesNotRead ++ falseOfOx110

  test("what is safe once a scope has ended is from assumptions of the kinds named".tag(Live)) {
    checked.map { (_, on) =>
      assertEquals(on("aClosedHerdRefusesToStart").sorted, theFlagRootIsFrom)
      safe.foreach(root => assertEquals(on(root).filterNot(named), Nil, root))
    }
  }

  test("what happens in time rests on nothing false of Ox 1.1.0, and on the code a fork is given ending".tag(Live)) {
    checked.map { (_, on) =>
      live.foreach { root =>
        assertEquals(on(root).filterNot(named ++ ofWhatHappensInTime ++ ofForkCode), Nil, root)
        assert(ofForkCode.forall(on(root).contains) && !on(root).contains("nothingIsAddedDuringTheLastCheck"), root)
      }
    }
  }

  test("that there is no data race rests on who reads and who writes a field, and on no value read".tag(Live)) {
    checked.map((_, on) => unraced.foreach((root, from) => assertEquals(on(root).sorted, from, root)))
  }

  test("that no thread is started rests on the platform and on the herd's flag being its own".tag(Live)) {
    checked.map { (_, on) =>
      // that adding stops rests on neither the code a fork is given nor the last check
      val adding = on("addingStopsOnceTheFlagIsSet")
      assert(!adding.exists(a => ofForkCode.contains(a) || a == "nothingIsAddedDuringTheLastCheck"), adding)
      onTheFlag.foreach(root =>
        assertEquals(on(root).filterNot(ofThePlatform), List("aHerdKeepsItsFlagToItself"), root))
      onTheLastCheck.foreach(n => assert(on(n).contains("nothingIsAddedDuringTheLastCheck"), n))
    }
  }

  test("the claims proven of Ox's code from the platform alone are those named".tag(Live)) {
    checked.map { (r, _) =>
      assertEquals(Ported.standing(r).collect { case (n, (assumed, Nil)) if assumed.forall(ofThePlatform) => n }
        .toList.sorted, provenOfTheCodeAlone.sorted)
    }
  }
