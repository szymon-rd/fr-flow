package rebac

import frflow.*
import java.util.concurrent.atomic.AtomicReference
import scala.collection.immutable.ListMap

/** The answer cache in memory: the newest answers by check and version, at most `cacheSize` of them; the project's own
  * code, tested against CacheModel (CacheKeepsAnswers).
  */
final class LruCache private (initial: ListMap[Ask, Boolean]) extends AnswerCache:
  // Newest first: a ListMap keeps insertion order, so the newest is put in front by rebuilding.
  private val held = AtomicReference(initial)

  /** What it keeps, newest first. */
  def entries: List[Cached] = held.get.toList.map((a, b) => Cached(a, b))
  def get(ask: Ask): Option[Boolean] = held.get.get(ask)
  def put(ask: Ask, answer: Boolean): Unit =
    held.updateAndGet(m => ListMap((ask -> answer) +: m.removed(ask).toList.take(cacheSize - 1)*))

  def lookup(a: Term[Ask]) = Flow.effect(a)(get)
  def remember(a: Term[Ask], answer: Term[Boolean]) = Flow.effect(a, answer)(put)

object LruCache:
  def holding(cs: List[Cached]): LruCache = LruCache(ListMap(cs.distinctBy(_.ask).take(cacheSize).map(c => c.ask -> c.answer)*))
