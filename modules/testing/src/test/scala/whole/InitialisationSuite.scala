package whole

import scala.concurrent.{Await, Future}
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration.*

/** The examples' files form a DAG (words, then boundaries, models and programs, then nodes, then the FrModel,
  * then the examples): each file's vals are set whichever is touched first, so two threads touching them in opposite
  * orders both finish. A cycle between two files would deadlock them, the JVM holding each file's initialisation for
  * the thread that began it.
  */
class InitialisationSuite extends munit.FunSuite:
  /** Each example's vals, from its first words to its FrModel, each read by touching it. */
  private val examples: List[(String, List[() => Any])] = List(
    "rooms" -> List(() => rooms.free, () => rooms.Bookings.bookWhenFree, () => rooms.rooms),
    "auth" -> List(() => auth.knowledge))

  test("each example's files initialise from two threads at once, one from its words, one from its FrModel") {
    examples.foreach { (name, vals) =>
      val both = Future(vals.map(_())).zip(Future(vals.reverse.map(_())))
      val (forward, backward) = Await.result(both, 60.seconds)
      assert(forward.forall(_ != null) && backward.forall(_ != null), name)
    }
  }
