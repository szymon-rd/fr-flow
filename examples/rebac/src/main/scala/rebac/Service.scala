package rebac

import cats.effect.SyncIO
import frflow.*
import java.util.concurrent.atomic.AtomicReference

/** The running service: one process holds the tuple store and the cache. A write is applied atomically and gets the
  * next version; a check runs CachedChecks' proven flow at a version no later than the latest, through the cache.
  * ServiceWiring governs this file.
  *
  * The cache stays sound across writes because the log only grows and a check never names a version past the latest:
  * the tuples of a version never change after it is written (Versions), so an answer kept for a version stays the
  * check's answer at that version.
  */
final class RebacService(schemaInForce: List[RelationDef], depth: List[Unit]):
  private val store = AtomicReference(TupleStore.empty)
  private val answers = LruCache.holding(Nil)

  /** One write or delete: the new version. */
  def write(w: Write): Int = store.updateAndGet(_.write(w)).version

  /** A check at the version asked, never past the latest (the latest if none is asked), through the cache. */
  def check(q: Query, at: Option[Int]): Boolean =
    val s = store.get
    val v = at.fold(s.version)(_.max(0).min(s.version))
    knowledge.run[SyncIO](cachedChecks)(cache.bind(answers), schema.bind(schemaInForce), levels.bind(depth),
      writes.bind(s.writes))(Ask(q, v)).unsafeRunSync()
