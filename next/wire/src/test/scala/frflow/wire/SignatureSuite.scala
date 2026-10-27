package frflow.wire

import frflow.core.name.NodeId
import frflow.decision.content.{Chain, Content, FieldValue}
import frflow.decision.ledger.{Action, Authorship, Bound, Decider, Deciders, Decision, Ledger, Reason, Seals}
import frflow.wire.file.Files
import frflow.wire.ledger.{DecidersFile, LedgerFile, SealCodecs}
import io.circe.Json
import java.time.Instant

/** Signatures survive the files, and a file whose signature is wrong or missing still reads, as a value the decision
  * rules refuse: a decision that does not count, a deciders' list that is not committed.
  */
class SignatureSuite extends munit.FunSuite:
  private val (ann, mallory) = (ThrowawayKey(), ThrowawayKey())
  private val verify = ThrowawayKey.verifier(ann, mallory)
  private val root = NodeId("Root")
  private val content = Content(List("kind" -> FieldValue.Text("claim"),
    "statement" -> FieldValue.Text("A room is booked only when free.")))

  private val first = signed(Deciders(List(Decider("ann", ann.id, ann.publicKey)), None, SealCodecs.unsigned), ann)
  private val ledger = Seals.signAdded(Ledger.empty, Ledger.empty.add(root, Decision.taken(Action.Accept,
    Authorship("ann", Instant.parse("2026-10-01T09:30:00.5Z"), Some("abc")), Reason("It states the purpose.", Nil),
    Bound(content, Chain("c1"), None))), ann.sign)

  private def signed(d: Deciders, key: ThrowawayKey): Deciders = d.copy(seal = key.sign(d.payload))
  private def counts(l: Ledger): Boolean = l.current(root).exists(first.counts(verify)(root, _))
  private def reread(l: Ledger): Ledger = Files.read(LedgerFile.format, Files.print(LedgerFile.format, l)).toOption.get
  private def edited(l: Ledger)(f: Json => Json): Ledger =
    Files.decode(LedgerFile.format, f(Files.json(LedgerFile.format, l))).fold(e => fail(e.toString), identity)
  private def seal(f: Json => Json)(j: Json): Json =
    j.hcursor.downField("decisions").downField("Root").downArray.downField("seal").withFocus(f).top.get

  test("a signed decision still counts once written and read") {
    assert(counts(ledger))
    assert(counts(reread(ledger)))
  }

  test("a ledger whose signature was changed reads, and its decision does not count") {
    val forged = mallory.sign("something else".getBytes).signature
    val wrong = edited(ledger)(seal(_.mapObject(_.add("signature", Json.fromString(forged)))))
    val garbled = edited(ledger)(seal(_.mapObject(_.add("signature", Json.fromString("not base64 at all!")))))
    assert(!counts(wrong))
    assert(!counts(garbled))
  }

  test("a ledger with no signature, or half of one, reads as unsigned, and its decision does not count") {
    val none = edited(ledger)(j => j.hcursor.downField("decisions").downField("Root").downArray.downField("seal")
      .delete.top.get)
    val half = edited(ledger)(seal(_.mapObject(_.remove("signature"))))
    assertEquals(none.current(root).flatMap(_.seal), None)
    assertEquals(half.current(root).flatMap(_.seal), None)
    assert(!counts(none) && !counts(half))
  }

  test("a decision signed by a key not listed under its decider's name does not count") {
    val other = Seals.signAdded(Ledger.empty, ledger.copy(decisions = ledger.decisions.view.mapValues(_.map(
      _.copy(seal = None))).toMap), mallory.sign)
    assert(!counts(reread(other)))
  }

  test("a content edited in the file reads, and the decisions bound to it do not count") {
    val ref = content.ref
    val changed = edited(ledger)(_.hcursor.downField("contents").downField(ref).downField("statement")
      .withFocus(_ => Json.fromString("A room is always booked.")).top.get)
    assertEquals(changed.current(root).map(_.bound.content.text("statement")), Some("A room is always booked."))
    assert(!counts(changed))
  }

  test("a signed deciders' list is committed once written and read; with another signature it is not") {
    val text = Files.print(DecidersFile.format, first)
    assertEquals(Files.read(DecidersFile.format, text).map(d => Deciders.committed(List(d), verify)),
      Right(Some(first)))
    val forged = text.replace(first.seal.signature, signed(first, mallory).seal.signature)
    assertEquals(Files.read(DecidersFile.format, forged).map(d => Deciders.committed(List(d), verify)), Right(None))
  }

  test("a deciders' list with no seal, or half of one, reads with a seal no key verifies, and is not committed") {
    val json = Files.json(DecidersFile.format, first)
    val none = Files.decode(DecidersFile.format, json.mapObject(_.remove("seal")))
    val half = Files.decode(DecidersFile.format,
      json.hcursor.downField("seal").withFocus(_.mapObject(_.remove("signature"))).top.get)
    assertEquals(none.map(_.seal), Right(SealCodecs.unsigned))
    assertEquals(half.map(_.seal), Right(SealCodecs.unsigned))
    List(none, half).foreach(d => assertEquals(d.map(x => Deciders.committed(List(x), verify)), Right(None)))
  }

  test("a later list signed by a key the list before held follows it through the files") {
    val next = signed(Deciders(first.entries :+ Decider("bob", mallory.id, mallory.publicKey), Some(first.ref),
      SealCodecs.unsigned), ann)
    val reread = Files.read(DecidersFile.format, Files.print(DecidersFile.format, next))
    assertEquals(reread.map(d => Deciders.committed(List(first, d), verify).map(_.entries.size)), Right(Some(2)))
  }
