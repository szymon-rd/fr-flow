package crm

import frflow.*
import java.util.concurrent.atomic.AtomicReference

/** The CRM's database in memory: the project's own code, for development and tests. It keeps the rows by record (a
  * map from a record's id to what the store holds about it) and the event log, and is tested against DatabaseModel
  * (TablesModel), as SQLite is checked against it.
  */
final class MemoryDatabase private (initial: MemoryDatabase.Held) extends Database:
  private val held = AtomicReference(initial)

  /** What it holds: the rows of each record, by id, and the event log. */
  def tables: Tables =
    val h = held.get
    val byId = h.rows.toList.sortBy(_._1).map(_._2)
    Tables(CrmStore(byId.flatMap(_.records), byId.flatMap(_.shares), byId.flatMap(_.expiries)), h.log.toList)

  def load = Flow.effect(tables.store)
  def storeAbout(id: Term[BigInt], t: Term[CrmStore]) =
    Flow.effect(id, t)((i, s) => { held.updateAndGet(h => h.copy(rows = MemoryDatabase.put(h.rows, i, s))); () })
  def logEvent(e: Term[Event]) = Flow.effect(e)(ev => { held.updateAndGet(h => h.copy(log = h.log :+ ev)); () })

object MemoryDatabase:
  private final case class Held(rows: Map[BigInt, CrmStore], log: Vector[Event])

  /** An in-memory database holding the given tables. */
  def holding(t: Tables): MemoryDatabase =
    val ids = (t.store.records.map(_.id) ++ t.store.shares.map(_.record) ++ t.store.expiries.map(_.record)).distinct
    MemoryDatabase(Held(ids.foldLeft(Map.empty[BigInt, CrmStore])((rows, id) => put(rows, id, t.store)), t.events.toVector))

  /** The rows `s` has about the record `id`, in place of those held about it. */
  private def put(rows: Map[BigInt, CrmStore], id: BigInt, s: CrmStore): Map[BigInt, CrmStore] =
    val about = CrmStore(s.records.filter(_.id == id), s.shares.filter(_.record == id), s.expiries.filter(_.record == id))
    if about.records.isEmpty && about.shares.isEmpty && about.expiries.isEmpty then rows.removed(id) else rows.updated(id, about)
