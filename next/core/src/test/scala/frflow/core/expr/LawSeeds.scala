package frflow.core.expr

/** The seeds the laws draw their terms from: `1 … n`, each suite's own `n`, or as `FRFLOW_LAW_SEEDS` says
  * (`from:count`), so a run (the nightly one) tries terms no other run has.
  */
object LawSeeds:
  def apply(n: Int): List[Long] = sys.env.get("FRFLOW_LAW_SEEDS").flatMap(parse).fold((1L to n.toLong).toList)(
    (from, count) => (from until from + count).toList)

  private def parse(s: String): Option[(Long, Long)] = s.split(':') match
    case Array(from, count) => from.toLongOption.zip(count.toLongOption).filter(_._2 > 0)
    case _                  => None
