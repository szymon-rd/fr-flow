package frflow.protocol

import io.circe.{Codec, Json}
import io.circe.parser.decode
import io.circe.syntax.*
import java.nio.file.{Files, Path, Paths}

/** The codecs: every type crossing modules and files reads back as written. */
class ProtocolSuite extends munit.FunSuite:

  private def roundTrip[A: Codec](a: A)(using munit.Location): Unit =
    assertEquals(decode[A](a.asJson.noSpaces), Right(a))

  private val content = Content("kind" -> Json.fromString("claim"), "parents" -> Json.arr(Json.fromString("Root")),
    "statement" -> Json.fromString("Readers  find\tthe books\n they ask for."), "formal" -> Json.False)

  test("statuses are written as words, and read back") {
    assertEquals(CheckStatus.ModelError.asJson, Json.fromString("model-error"))
    assertEquals(ObligationStatus.NotNeeded.toString, "not-needed")
    assertEquals(ObligationStatus.NoClash.toString, "no-clash")
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

  test("tries: what Lean proving each means, and their words when it does not") {
    assertEquals((TryKind.Needed("A").onProven, TryKind.Needed("A").onNot), (ObligationStatus.NotNeeded, ObligationStatus.Needed))
    assert(TryKind.Clash.fatal && TryKind.Unsat.fatal && !TryKind.Idle.fatal)
    assertEquals(TryKind.Vacuous.unshown("Root", "Part", ""), "Lean found no proof that Root holds whatever Part says (a try)")
    assertEquals(TryKind.VacuousExpect(0).onProven, ObligationStatus.Vacuous)
  }

  private val decision = Decision(Action.Accept, "dev", "2026-01-01T00:00:00Z", "it is right", rejected = List(NodeId("Alt")),
    code = Some(Fingerprint("f")), chain = Chain("c"), content = content)

  test("a ledger reads back as written; content repeated for a node is written once") {
    val again = decision.copy(action = Action.Confirm, at = "2026-01-02T00:00:00Z", rejected = Nil)
    val l = Ledger.empty.add(NodeId("A"), decision).add(NodeId("A"), again).add(NodeId("Alt"), decision.copy(action = Action.Reject))
    val text = Canonical.file(l.asJson)
    assert(text.contains("\"content\": \"same:"), text)
    assert(!text.contains("null") && !text.contains("\"rejected\": []"), text)
    assertEquals(decode[Ledger](text), Right(l))
    assertEquals(l.history(NodeId("A")).last.after, Some(Ledger.entry(decision)))
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

  test("checks, requests and decision requests read back as written") {
    roundTrip(NodeCheck(Hash("h"), CheckStatus.Proven, List(Result("complete", ObligationStatus.Proven, "auto"),
      Result("needed_A", ObligationStatus.Needed)), Nil, List("propext"), "2026-01-01T00:00:00Z"))
    roundTrip(Request(RequestId("R1"), None, "Say more.", "dev", "2026-01-01T00:00:00Z", RequestStatus.Open))
    roundTrip(DecisionRequest(NodeId("A"), "dev", "it is right", reject = List(NodeId("B")), seen = Some("v")))
  }

  test("a snapshot and its review read back as written") {
    val node = SnapNode(NodeId("A"), NodeKind.Contract, content, content.hash, parents = List(NodeId("Root")),
      status = Some(CheckStatus.Open), examples = List(ExampleView("one", List("x = 1"), "f(1)", true, "ok", Some("ok"),
        Some(Outcome(ObligationStatus.Proven, "Lean agrees")), None)),
      code = Some(CodeRef(List("A.scala"), Fingerprint("f"))),
      split = Some(Split(Outcome.unchecked, List(Split.Part(NodeId("B"), ObligationStatus.Needed, "")), Outcome(ObligationStatus.NoClash))),
      invariants = List(Kept(NodeId("I"), "view", "rule", ObligationStatus.Exempt, "why")))
    val snap = Snapshot("Shelf", List(node), root = Some(NodeId("Root")), params = List(ParamTerm("good", "good", false, None, "Book → Bool")))
    roundTrip(snap)
    val review = Review(ReviewState.Review, List(Cause.Above), "v", Some(NodeId("Root")), List(Moved(NodeId("Root"), content)),
      Some(decision), Some("it is right"), None, Nil, Nil, Nil, Nil,
      List(Below(NodeId("B"), BelowKind.Moved, "s", "r", "c", "w")), List(decision), Nil, List(Alternative(NodeId("Alt"), content)))
    roundTrip(Annotated(snap, List(Reviewed(node, review)), List(Gone(NodeId("Old"), decision)), List(NodeId("A"))))
    assert(review.mechanical)
  }
