package frflow.wire

import frflow.core.name.NodeId
import frflow.decision.content.{Chain, CodeFingerprint, Content, FieldValue}
import frflow.decision.ledger.{Action, Authorship, Bound, Decider, Deciders, Decision, EntryRef, Ledger, Reason, Seal}
import java.time.Instant

/** The golden ledger and deciders' list: two nodes, a decision with every field and one with none of the optional
  * ones, two decisions bound to one content. The seals are stand-ins; `SignatureSuite` signs with real keys.
  */
object LedgerSamples:
  private val root = Content(List("kind" -> FieldValue.Text("claim"), "parents" -> FieldValue.Texts(Nil),
    "parts" -> FieldValue.Texts(List("Free")), "statement" -> FieldValue.Text("A room is booked only when free."),
    "formula" -> FieldValue.Text("forall b. booked(b) implies free(b)"),
    "vocabulary" -> FieldValue.Texts(List("booked: a booking was made", "free: no booking overlaps"))))

  private val free = Content(List("kind" -> FieldValue.Text("design"), "parents" -> FieldValue.Texts(List("Root")),
    "statement" -> FieldValue.Text("Bookings are kept in one store."),
    "implementations" -> FieldValue.Record(List("store" -> "Store.scala", "model" -> "StoreModel.scala"))))

  private val accepted = Decision(Action.Accept,
    Authorship("ann", Instant.parse("2026-10-01T09:30:00.123456Z"), Some("5dfd26d3e3a4e189330405ba025c7b408c8e0d6b")),
    Reason("What booking answers, as a root of its own.", List(NodeId("OldRoot"))),
    Bound(root, Chain("c182d4664cd771bde270bc06bb7b1c02d3cd4587b07e325daa988d872e330b9d"),
      Some(CodeFingerprint("72303c354a89bf8df28b567ff2bcf59b7ca049b961f690e4362d22bee343f311"))),
    None, Some(Seal("b6e216cfdf46a202", "c2lnbmF0dXJlIG9mIHRoZSBmaXJzdA==")))

  private val revisited = Decision(Action.Revisit, Authorship("ann", Instant.parse("2026-10-02T10:00:00Z"), None),
    Reason("The store's model moved under it.", Nil), Bound(root, Chain.empty, None),
    Some(EntryRef("6f9c9389fbe749eb")), None)

  private val design = Decision(Action.Accept, Authorship("bob", Instant.parse("2026-10-01T11:00:00Z"), None),
    Reason("One store, its model beside it.", Nil), Bound(free, Chain("96c938af291fdd94"), None), None,
    Some(Seal("0123456789abcdef", "c2lnbmF0dXJlIG9mIHRoZSBkZXNpZ24=")))

  val ledger: Ledger = Ledger(Map(NodeId("Root") -> List(accepted, revisited), NodeId("Free") -> List(design)))

  val deciders: Deciders = Deciders(List(Decider("ann", "b6e216cfdf46a202", "MCowBQYDK2VwAyEAann"),
    Decider("bob", "0123456789abcdef", "MCowBQYDK2VwAyEAbob")), Some("9a0b1c2d3e4f5a6b"),
    Seal("b6e216cfdf46a202", "c2lnbmF0dXJlIG9mIHRoZSBsaXN0"))
