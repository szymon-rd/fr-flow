package rebac

/** The tuple store in memory, standing for a database: a log of writes, and an index by object of the tuples each
  * version leaves. A read at a version replays only that object's writes up to it. StoreIndex is assumed of it, and it
  * is checked against StoreIndex on the examples and on generated logs.
  */
final class TupleStore private (log: Vector[Write], byObject: Map[Obj, Vector[(Int, Write)]]):
  /** The writes so far, in order. */
  def writes: List[Write] = log.toList
  def version: Int = log.size

  /** The tuples about `o` that the first `v` writes leave, in the order they were added. */
  def tuplesOf(v: Int, o: Obj): List[RelTuple] =
    byObject.getOrElse(o, Vector.empty).takeWhile(_._1 <= v).foldLeft(Vector.empty[RelTuple]) {
      case (ts, (_, Write.Add(t)))    => if ts.contains(t) then ts else ts :+ t
      case (ts, (_, Write.Remove(t))) => ts.filterNot(_ == t)
    }.toList

  /** The store after one more write: its version is the new length of the log. */
  def write(w: Write): TupleStore =
    val obj = w match
      case Write.Add(t)    => t.obj
      case Write.Remove(t) => t.obj
    TupleStore(log :+ w, byObject.updated(obj, byObject.getOrElse(obj, Vector.empty) :+ (log.size + 1, w)))

object TupleStore:
  val empty: TupleStore = TupleStore(Vector.empty, Map.empty)
  def replaying(ws: List[Write]): TupleStore = ws.foldLeft(empty)(_.write(_))

