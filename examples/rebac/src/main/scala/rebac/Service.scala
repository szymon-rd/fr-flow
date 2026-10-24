package rebac

import cats.effect.SyncIO
import frflow.*
import java.util.concurrent.atomic.AtomicReference

/** What makes a schema unusable: a kind and relation defined twice (which definition would a check read?). */
object Schema:
  def problems(defs: List[RelationDef]): List[String] =
    defs.groupBy(d => (d.kind, d.rel)).collect { case ((k, r), ds) if ds.size > 1 => s"$k#$r is defined ${ds.size} times" }.toList.sorted

/** The running service: one process holds the tuple store and the cache. A write is applied atomically and gets the
  * next version; a check runs CachedChecks' proven flow at a version from 0 to the latest, through the cache.
  * ServiceWiring governs this file.
  *
  * The cache stays sound across writes because the log only grows and a check never names a version past the latest:
  * the tuples of a version never change after it is written (Versions), so an answer kept for a version stays the
  * check's answer at that version.
  */
final class RebacService(schemaInForce0: List[RelationDef], depth: List[Unit]) extends Backend:
  require(Schema.problems(schemaInForce0).isEmpty, s"the schema is unusable: ${Schema.problems(schemaInForce0).mkString("; ")}")
  private val store = AtomicReference(TupleStore.empty)
  private val answers = LruCache.holding(Nil)

  def schemaInForce: List[RelationDef] = schemaInForce0
  def latest: Int = store.get.version

  /** One write or delete: the new version. */
  def write(w: Write): Int = store.updateAndGet(_.write(w)).version

  /** The check at version `v` (from 0 to the latest), through the cache. */
  def allowed(q: Query, v: Int): Boolean =
    val s = store.get
    require(v >= 0 && v <= s.version, s"version $v is not from 0 to ${s.version}")
    knowledge.run[SyncIO](cachedChecks)(cache.bind(answers), schema.bind(schemaInForce0), levels.bind(depth),
      writes.bind(s.writes))(Ask(q, v)).unsafeRunSync()
