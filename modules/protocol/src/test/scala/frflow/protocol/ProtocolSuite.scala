package frflow.protocol

import io.circe.{Codec, Json}
import io.circe.parser.decode
import io.circe.syntax.*
import java.nio.file.{Files, Path, Paths}
import java.time.Instant

/** The codecs (every type crossing modules and files reads back as written), the hashes, and the walks. */
class ProtocolSuite extends munit.FunSuite:

  private def roundTrip[A: Codec](a: A)(using munit.Location): Unit =
    assertEquals(decode[A](a.asJson.noSpaces), Right(a))

  private val content = Content("kind" -> Json.fromString("claim"), "parents" -> Json.arr(Json.fromString("Root")),
    "statement" -> Json.fromString("Readers  find\tthe books\n they ask for."), "formal" -> Json.False)

  test("statuses are written as words, and read back") {
    assertEquals((CheckStatus.ModelError.asJson, ObligationStatus.NotShown.toString), (Json.fromString("model-error"), "not-shown"))
    assert(decode[Action]("\"settle\"").isLeft)
    List(NodeKind.values, CheckStatus.values, ObligationStatus.values, ReviewState.values, Cause.values, Action.values,
      BelowKind.values).foreach(_.foreach(v => assertEquals(v.toString, v.toString.toLowerCase)))
    NodeKind.values.foreach(roundTrip(_)); CheckStatus.values.foreach(roundTrip(_)); ObligationStatus.values.foreach(roundTrip(_))
  }

  test("the canonical printing is compact, in field order; hashing ignores runs of whitespace") {
    assertEquals(Canonical.print(content.json),
      """{"kind":"claim","parents":["Root"],"statement":"Readers  find\tthe books\n they ask for.","formal":false}""")
    assertEquals(Canonical.print(Json.obj("n" -> Json.fromInt(3), "x" -> Json.fromDoubleOrNull(1.5), "c" -> Json.fromString("\u0001\"\\"))),
      """{"n":3,"x":1.5,"c":"\u0001\"\\"}""")
    val spaced = content.mapFields { case ("statement", _) => "statement" -> Json.fromString("Readers find the books they ask for.") }
    assertEquals(spaced.hash, content.hash)
    assertNotEquals(spaced.ref, content.ref)
    assertEquals(content.parents, List(NodeId("Root")))
    assertEquals(content.parts, None)
  }

  test("tries and obligation names: which fail the node, their words, their names read back") {
    assert(TryKind.Clash.fatal && TryKind.Unsat.fatal && !TryKind.Idle.fatal)
    assertEquals(TryKind.Vacuous.unshown("Root", "Part", ""), "Lean found no proof that Root holds whatever Part says (a try)")
    val names = List(ObligationName.Complete, ObligationName.Feasible, ObligationName.Impl, ObligationName.Check, ObligationName.RootImpl,
      ObligationName.Cover("Isolated"), ObligationName.Expect(2), ObligationName.Eval(0), ObligationName.EvalImpl(3), ObligationName.Probe(1),
      ObligationName.ProbeImpl(5)) ++ List(TryKind.Needed("A_b"), TryKind.Vacuous, TryKind.Restates, TryKind.Clash, TryKind.Unsat, TryKind.Idle,
      TryKind.VacuousExpect(1), TryKind.RestatesConjunct("A_b", 12)).map(ObligationName.Tried(_))
    assertEquals(names.map(n => ObligationName.parse(n.lean)), names.map(Some(_)))
    assertEquals(names.map(_.lean).take(7), List("complete", "feasible", "impl", "check", "root_impl", "cover_Isolated", "expect_2"))
    assertEquals(ObligationName.Tried(TryKind.VacuousExpect(1)).lean, "vacuous_expect_1")
    assertEquals(ObligationName.parse("holds"), None)
    assert(ObligationName.Probe(1).isEvaluation && ObligationName.Probe(1).isProbe && ObligationName.EvalImpl(0).isEvaluation)
    assert(!ObligationName.Complete.isEvaluation && !ObligationName.Eval(0).isProbe)
    assertEquals(ObligationName.Probe(2).ofCode, ObligationName.ProbeImpl(2))
  }

  private val decision = Decision(Action.Accept, "dev", Instant.parse("2026-01-01T00:00:00Z"), "it is right", rejected = List(NodeId("Alt")),
    code = Some(Fingerprint("f")), chain = Chain("c"), content = content)

  test("a ledger reads back as written; decisions are ordered by when they were taken, to the nanosecond") {
    val again = decision.copy(action = Action.Confirm, at = Instant.parse("2026-01-01T00:00:00.4Z"), rejected = Nil)
    val l = Ledger.empty.add(NodeId("A"), again).add(NodeId("A"), decision).add(NodeId("Alt"), decision.copy(action = Action.Reject))
    val text = Canonical.file(l.asJson)
    assert(!text.contains("null"), text)
    assertEquals(l.all.map(_._2.at), List(again.at, decision.at, decision.at))
    assertEquals(decode[Ledger](text), Right(l))
    assertEquals(l.history(NodeId("A")).last.after, Some(Ledger.entry(again)))
  }

  /** The examples' committed files, found from wherever the tests run. */
  private def examples: Path =
    Iterator.iterate(Paths.get("").toAbsolutePath)(_.getParent).takeWhile(_ != null).map(_.resolve("examples"))
      .find(p => Files.isDirectory(p.resolve("auth"))).getOrElse(fail("no examples directory"))

  test("the examples' committed ledgers and requests read, and are written back as they are") {
    List("auth", "keycloak", "crm").foreach { e =>
      val file = examples.resolve(s"$e/.frflow/ledger.json")
      val text = Files.readString(file)
      val l = decode[Ledger](text).fold(err => fail(s"$file: $err"), identity)
      assert(l.decisions.nonEmpty)
      assertEquals(Canonical.file(l.asJson) + "\n", text, file)
    }
  }

  test("checks, a snapshot and its review read back as written") {
    roundTrip(NodeCheck(Hash("h"), CheckStatus.Proven, List(Result(ObligationName.Complete, ObligationStatus.Proven, "auto"),
      Result(ObligationName.Tried(TryKind.Needed("A")), ObligationStatus.NotShown)), Nil, List("propext"), decision.at))
    val node = SnapNode(NodeId("A"), NodeKind.Contract, content, content.hash, parents = List(NodeId("Root")),
      status = Some(CheckStatus.Open), examples = List(ExampleView("one", List("x = 1"), "f(1)", true, None, None,
        Some(Outcome(ObligationStatus.Proven, "Lean agrees")), None)),
      code = Some(CodeRef(List("A.scala"), Fingerprint("f"))),
      split = Some(Split(Outcome.unchecked, List(Split.Part(NodeId("B"), ObligationStatus.NotShown, "")), Outcome(ObligationStatus.NotShown))),
      invariants = List(Kept(NodeId("I"), "view", "rule", ObligationStatus.Exempt, "why")))
    val snap = Snapshot("Shelf", List(node), root = Some(NodeId("Root")), params = List(ParamTerm("good", "good", false, None, "Book → Bool")))
    roundTrip(snap)
    val review = Review(ReviewState.Review, List(Cause.Above), Version("v"), Some(NodeId("Root")), List(Moved(NodeId("Root"), content)),
      Some(decision), Some(decision), Some("it is right"), None, Nil, Nil,
      List(Below(NodeId("B"), BelowKind.Moved, "s", "r", "c", "w")), List(decision), Nil, List(Alternative(NodeId("Alt"), content)))
    roundTrip(Annotated(snap, List(Reviewed(node, review)), List(Gone(NodeId("Old"), decision)), List(NodeId("A"))))
    assert(review.mechanical)
  }

  test("the walks, on a diamond with a cycle: breadth first, preorder, and postorder cut where the cycle closes") {
    // a → b, c; b → d; c → d; d → a; e alone
    val edges = Map("a" -> List("b", "c"), "b" -> List("d"), "c" -> List("d"), "d" -> List("a"), "e" -> Nil)
    def next(v: String) = edges.getOrElse(v, Nil)
    assertEquals(Walk.breadthFirst(next("a"), identity)(next), List("b", "c", "d", "a"))
    assertEquals(Walk.breadthFirst(List("e"), identity)(next), List("e"))
    assertEquals(Walk.preorder(List("a"), identity)(next), List("a", "b", "d", "c"))
    assertEquals(Walk.postorder(List("a", "e"), identity)(next), List("d", "b", "c", "a", "e"))
    // by key: two values with one key are one
    assertEquals(Walk.postorder(List("x1", "x2", "y"), _.head)(_ => Nil), List("x1", "y"))
  }
