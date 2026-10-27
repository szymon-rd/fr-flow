package frflow.eval.flow

import cats.Id
import cats.effect.{IO, Ref}
import java.io.IOException

/** The shelf as plain Scala, as an adapter is written: each call takes the next of `faults`, and on `true` fails with
  * an `IOException`, changing nothing; otherwise the numbers in `held`, oldest first.
  */
final class PlainShelf(held: Ref[IO, List[BigInt]], faults: Ref[IO, List[Boolean]]) extends Shelf[IO, Id]:
  def items: IO[List[BigInt]] = fault(held.get)
  def put(n: BigInt): IO[Unit] = fault(held.update(_ :+ n))

  private def fault[A](call: IO[A]): IO[A] = faults.modify(fs => (fs.drop(1), fs.headOption.contains(true)))
    .flatMap(fails => if fails then IO.raiseError(IOException("the shelf is down")) else call)
