package frflow.eval.flow

import cats.effect.{IO, Ref}
import cats.syntax.all.*
import java.io.IOException

/** The shelf as plain Scala: each call takes the next of `faults`, and on `true` fails with an `IOException`,
  * changing nothing; otherwise the numbers in `numbers`, oldest first.
  */
final class PlainShelf(numbers: Ref[IO, List[BigInt]], faults: Ref[IO, List[Boolean]]):
  def items: IO[List[BigInt]] = fault(numbers.get)
  def put(n: BigInt): IO[Unit] = fault(numbers.update(_ :+ n))
  /** What it holds, read back. */
  def held: IO[List[BigInt]] = numbers.get

  private def fault[A](call: IO[A]): IO[A] = faults.modify(fs => (fs.drop(1), fs.headOption.contains(true)))
    .flatMap(fails => if fails then IO.raiseError(IOException("the shelf is down")) else call)

object PlainShelf:
  /** A shelf holding `numbers`, never down. */
  def holding(numbers: List[BigInt]): IO[PlainShelf] =
    (IO.ref(numbers), IO.ref(List.empty[Boolean])).mapN(PlainShelf(_, _))
