package rebac

import frflow.*

// ============================================================================
// The cache: a boundary the check is served through, decided as a state model
// ============================================================================

/** An answer the cache keeps, for a check at a version. */
final case class Cached(ask: Ask, answer: Boolean)
object Cached extends Data[Cached]

/** What proven code may ask of the cache. */
trait AnswerCache:
  /** The answer kept for the check at its version, if any. */
  def lookup(a: Term[Ask]): Flow[Option[Boolean]]
  /** Keeps the answer for the check at its version, in place of any it kept for it. */
  def remember(a: Term[Ask], answer: Term[Boolean]): Flow[Unit]

val cache = Boundary[AnswerCache]("cache", "the service's cache of answers, kept by check and version, in the service's memory")

/** How many answers the cache keeps: the newest, by when they were kept. */
val cacheSize = 1024

/** The cache as the proofs see it: the answers it keeps, newest first. */
object CacheModel extends AnswerCache, StateModel[List[Cached]]:
  def lookup(a: Term[Ask]) =
    state.get.map(cs => cs.find(c => c.ask === a).on[Some[Cached]](c => some(c.answer)).on[None.type](none[Boolean]))
  def remember(a: Term[Ask], answer: Term[Boolean]) =
    state.update(cs => (Cached(a, answer) :: cs.filterNot(c => c.ask === a)).take(cacheSize))

val cacheKeepsAnswers = Node.assumption(cache)(CacheModel)("CacheKeepsAnswers",
  "The cache gives back the answer it last kept for a check at a version, if it still keeps it, and keeps the newest answers, a bounded number of them.",
  why = "Answers are kept by the check and its version, so a later write, which makes a new version, never meets an answer kept for an older one: staleness, the classic bug of an authorization cache, cannot happen by how the key is made (Q4), since the tuples of a version never change (Versions, ServiceWiring). The cache is the service's own code (LruCache.scala), tested against this model on generated runs of its operations; what is decided here is the model.",
  idea = "Versions and the cache")
  .implementedBy(cs => LruCache.holding(cs), _.entries)

/** Whether every answer the cache keeps is the answer the check gives for its check and version. */
val cacheSound = define { (cs: Term[List[Cached]]) => cs.forall(c => c.answer === allowed(c.ask.query, c.ask.at)) }

val runCheck = Param[Ask => Flow[Boolean]]("runCheck",
  "a check served through the cache: what a client's request runs")

/** A check through the cache: the kept answer if there is one, or the check's, kept for next time. */
def cachedCheck(a: Term[Ask]): Flow[Boolean] =
  for
    hit <- cache.lookup(a)
    answer <- If(hit.isDefined)(Flow.pure(hit.getOrElse(False))).Else(
      for
        fresh <- Flow.pure(allowed(a.query, a.at))
        _     <- cache.remember(a, fresh)
      yield fresh)
  yield answer

private val annAt3 = Ask(Query(Obj("doc", "readme"), "viewer", "ann"), 3)
private val annAt5 = Ask(Query(Obj("doc", "readme"), "viewer", "ann"), 5)

val cachedChecks = Node.contract(runCheck)("CachedChecks",
  "A check served through the cache answers what the check gives at its version, and leaves the cache keeping only answers the check gives, when it kept only such answers before.",
  why = "The cache must never change an answer (Q4): served from the cache or not, a check answers as CheckContract says. Proven of the code from the cache's model (CacheKeepsAnswers) and the check's contract; the cache's soundness is what a run keeps, so a sequence of runs keeps it.",
  idea = "Versions and the cache"
)((a, result, before, after) =>
  cacheSound(before(CacheModel)) ==> (result === allowed(a.query, a.at) && cacheSound(after(CacheModel))))
  .examples(schema.bind(demoSchema), levels.bind(demoLevels), writes.bind(demoWrites))(
    expect(annAt3, World(CacheModel -> Nil), true, World(CacheModel -> List(Cached(annAt3, true))),
      "a miss: the check is resolved, answered, and kept"),
    expect(annAt5, World(CacheModel -> List(Cached(annAt3, true))), false,
      World(CacheModel -> List(Cached(annAt5, false), Cached(annAt3, true))),
      "a later version is another key: the answer kept at version 3 is not used at version 5"),
    expect(annAt3, World(CacheModel -> List(Cached(annAt3, true))), true, World(CacheModel -> List(Cached(annAt3, true))),
      "a hit: the kept answer, and the cache unchanged"),
    reject(annAt5, World(CacheModel -> List(Cached(annAt3, true))), true,
      World(CacheModel -> List(Cached(annAt5, true), Cached(annAt3, true))),
      "an answer kept for version 3 never answers a check at version 5"))
