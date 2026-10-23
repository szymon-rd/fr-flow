package frflow.protocol

import io.circe.{Codec, Json}
import io.circe.parser.decode
import io.circe.syntax.*
import java.nio.file.{Files, Path, Paths}
import java.time.Instant

/** The codecs: every type crossing modules and files reads back as written. */
class ProtocolSuite extends munit.FunSuite:

  private def roundTrip[A: Codec](a: A)(using munit.Location): Unit =
    assertEquals(decode[A](a.asJson.noSpaces), Right(a))

  private val content = Content("kind" -> Json.fromString("claim"), "parents" -> Json.arr(Json.fromString("Root")),
    "statement" -> Json.fromString("Readers  find\tthe books\n they ask for."), "formal" -> Json.False)

  test("statuses are written as words, and read back") {
    assertEquals(CheckStatus.ModelError.asJson, Json.fromString("model-error"))
    assertEquals(ObligationStatus.NotShown.toString, "not-shown")
    assertEquals(decode[Cause]("\"self\""), Right(Cause.Self))
    assert(decode[Action]("\"settle\"").isLeft)
    List(NodeKind.values, CheckStatus.values, ObligationStatus.values, ReviewState.values, Cause.values, Action.values,
      RequestStatus.values, BelowKind.values).foreach(_.foreach(v => assertEquals(v.toString, v.toString.toLowerCase)))
    NodeKind.values.foreach(roundTrip(_)); CheckStatus.values.foreach(roundTrip(_)); ObligationStatus.values.foreach(roundTrip(_))
    assertEquals(NodeKind.Claim.shown(rule = true), "invariant")
  }

  test("the canonical printing is compact, in field order; hashing ignores runs of whitespace") {
    assertEquals(Canonical.print(content.json),
      """{"kind":"claim","parents":["Root"],"statement":"Readers  find\tthe books\n they ask for.","formal":false}""")
    assertEquals(Canonical.print(Json.obj("n" -> Json.fromInt(3), "x" -> Json.fromDoubleOrNull(1.5), "c" -> Json.fromString("\u0001"))),
      """{"n":3,"x":1.5,"c":"\u0001"}""")
    val spaced = content.mapFields { case ("statement", _) => "statement" -> Json.fromString("Readers find the books they ask for.") }
    assertEquals(spaced.hash, content.hash)
    assertNotEquals(spaced.ref, content.ref)
    assertEquals(content.parents, List(NodeId("Root")))
    assertEquals(content.parts, None)
  }

  test("tries: which fail the node, their words when Lean finds no proof, and their names") {
    assert(TryKind.Clash.fatal && TryKind.Unsat.fatal && !TryKind.Idle.fatal)
    assertEquals(TryKind.Vacuous.unshown("Root", "Part", ""), "Lean found no proof that Root holds whatever Part says (a try)")
    List(ObligationName.Tried(TryKind.Needed("A")), ObligationName.Cover("I"), ObligationName.EvalImpl(3), ObligationName.RootImpl,
      ObligationName.Tried(TryKind.VacuousExpect(2))).foreach(o => assertEquals(ObligationName.parse(o.lean), Some(o)))
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
    val requests = decode[List[Request]](Files.readString(examples.resolve("keycloak/.frflow/requests.json")))
    assertEquals(requests.map(_.map(_.status)), Right(List(RequestStatus.Closed)))
  }

  test("checks and requests read back as written") {
    roundTrip(NodeCheck(Hash("h"), CheckStatus.Proven, List(Result(ObligationName.Complete, ObligationStatus.Proven, "auto"),
      Result(ObligationName.Tried(TryKind.Needed("A")), ObligationStatus.NotShown)), Nil, List("propext"), decision.at))
    roundTrip(Request(RequestId("R1"), None, "Say more.", "dev", decision.at, RequestStatus.Open))
  }

  test("a snapshot and its review read back as written") {
    val node = SnapNode(NodeId("A"), NodeKind.Contract, content, content.hash, parents = List(NodeId("Root")),
      status = Some(CheckStatus.Open), examples = List(ExampleView("one", List("x = 1"), "f(1)", true, None, None,
        Some(Outcome(ObligationStatus.Proven, "Lean agrees")), None)),
      code = Some(CodeRef(List("A.scala"), Fingerprint("f"))),
      split = Some(Split(Outcome.unchecked, List(Split.Part(NodeId("B"), ObligationStatus.NotShown, "")), Outcome(ObligationStatus.NotShown))),
      invariants = List(Kept(NodeId("I"), "view", "rule", ObligationStatus.Exempt, "why")))
    val snap = Snapshot("Shelf", List(node), root = Some(NodeId("Root")), params = List(ParamTerm("good", "good", false, None, "Book → Bool")))
    roundTrip(snap)
    val review = Review(ReviewState.Review, List(Cause.Above), "v", Some(NodeId("Root")), List(Moved(NodeId("Root"), content)),
      Some(decision), Some(decision), Some("it is right"), None, Nil, Nil,
      List(Below(NodeId("B"), BelowKind.Moved, "s", "r", "c", "w")), List(decision), Nil, List(Alternative(NodeId("Alt"), content)))
    roundTrip(Annotated(snap, List(Reviewed(node, review)), List(Gone(NodeId("Old"), decision)), List(NodeId("A"))))
    assert(review.mechanical)
  }
