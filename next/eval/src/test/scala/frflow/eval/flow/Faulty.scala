package frflow.eval.flow

import cats.effect.{IO, Ref}
import frflow.*
import frflow.dsl.term.Lift

/** The shelf failing as its boundary says it may: each call takes the next of `faults`, and on `true` fails with
  * `Trouble.Down`, raised as programs raise it, changing nothing; otherwise it is `shelf`'s.
  */
final class Faulty(shelf: Shelf[IO, Term], faults: Ref[IO, List[Boolean]], flow: Flow[IO]) extends Shelf[IO, Term]:
  def items: IO[Term[List[BigInt]]] = fault(shelf.items)
  def put(n: Term[BigInt]): IO[Unit] = fault(shelf.put(n))

  private def fault[A](call: IO[A]): IO[A] = faults.modify(fs => (fs.drop(1), fs.headOption.contains(true)))
    .flatMap(fails => if fails then flow.raise[Trouble, A](Lift.constant(Trouble.Down)) else call)
