package frflow.wire

import frflow.wire.snapshot.*

/** The golden snapshot: a claim tested and proven in part, a design, a consistency group and an example. */
object SnapshotSamples:
  private val book = SnapNode(
    Header("Book", "claim", "9f8e7d", List("kind" -> FieldRow.Text("claim"), "parts" -> FieldRow.Texts(Nil),
      "statement" -> FieldRow.Text("Booking a free room books it."))),
    PlaceRow(List("Root"), Nil, List("StoreBehaves"), List("free"), Nil),
    CheckRow("open", "∀ b, book b", List(ObligationRow("impl", "open", "theorem impl : Obl.impl"))),
    Body.Stated(List("as a call of book"), Some("book"), Some(CodeRow(List("free"), List("plain"), Nil)),
      Some(TestRow(500, 42L, "claim Book", true))))

  private val store = SnapNode(
    Header("Store", "design", "1a2b3c", List("implementations" -> FieldRow.Record(List("store" -> "Store.scala")))),
    PlaceRow(List("Root"), Nil, Nil, Nil, List("bookings")), CheckRow("proven", "", Nil),
    Body.Design(List("Store.scala")))

  val snapshot: Snapshot = Snapshot("Rooms", List("Root"), List("StoreBehaves"),
    List(TermRow("free", "no booking overlaps the request")), List(book, store),
    List(GroupRow(List("Book"), List("free"), List("rooms"), List("free: the equation of Book"), "witnessed")),
    List(ExampleRow("Oak at ten", "proven", "holds")))
