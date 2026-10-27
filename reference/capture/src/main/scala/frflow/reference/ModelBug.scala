package frflow.reference

import _root_.crm.*
import frflow.{Flow, KnowledgeBase, Node, Term}

/** crm's in-memory store that keeps a record's old shares, a copy of `CrmSuite`'s (`var` and all): found by the model
  * test.
  */
object ModelBug:
  /** Holds the rows a store has about a record in place of the record's rows, but keeps its old shares. */
  final class LeakyDatabase(start: Tables) extends Database:
    private var t = start
    def tables: Tables = t
    def load = Flow.effect(t.store)
    def storeAbout(id: Term[BigInt], s: Term[CrmStore]) = Flow.effect(id, s) { (i, x) =>
      t = t.copy(store = CrmStore(t.store.records.filter(_.id != i) ++ x.records.filter(_.id == i),
        t.store.shares ++ x.shares.filter(_.record == i),
        t.store.expiries.filter(_.record != i) ++ x.expiries.filter(_.record == i)))
    }
    def logEvent(e: Term[Event]) = Flow.effect(e)(ev => { t = t.copy(events = t.events :+ ev) })

  private val original = _root_.crm.tablesModel

  def leakyStore: Seeded =
    // Named as the suite names it, so that the node keeps its id.
    val tablesModel = Node.assumption(db)(DatabaseModel)(original.statement, original.why)
      .implementedBy(t => LeakyDatabase(t), _.tables)
    val kb = KnowledgeBase(knowledge.name, knowledge.idea, knowledge.implementations, knowledge.generators,
      knowledge.testing)(knowledge.nodes.map(n => if n eq original then tablesModel else n)*)
    Seeded("in-memory store that keeps a record's old shares", inTable = false,
      "the Database's own in-memory implementation keeps the shares of a record it stores again",
      "CrmSuite: a seeded bug in an in-memory store (a record's old shares kept) is found by generated runs and shrunk",
      Stops.generated(kb, tablesModel))
