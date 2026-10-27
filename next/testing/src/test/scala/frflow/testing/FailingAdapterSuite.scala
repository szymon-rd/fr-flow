package frflow.testing

import cats.Id
import cats.effect.{IO, Ref}
import cats.syntax.all.*
import cats.effect.unsafe.implicits.global
import frflow.core.name.OpName
import frflow.eval.{ScalaValue, Semantics}
import frflow.eval.flow.{PlainShelf, Shelf}
import frflow.testing.model.{Difference, ModelTests, Step}

/** A failing boundary's adapter in a model test: its failure is the boundary's declared error, as production's
  * `lifted` makes it (`BoundaryOps.failures`), so it is compared with the model as a program would see it.
  */
class FailingAdapterSuite extends munit.FunSuite:
  private val elaborated = Shelf.knowledge.elaborated.fold(es => fail(es.toString), identity)
  private val semantics = Semantics(elaborated)
  private val run = List(Step(Shelf.shelf.name, OpName("put"), List(ScalaValue(BigInt(4)))),
    Step(Shelf.shelf.name, OpName("items"), Nil))

  /** The plain shelf, its numbers read back. */
  private final class Read(val held: Ref[IO, List[BigInt]], faults: Ref[IO, List[Boolean]]) extends Shelf[IO, Id]:
    private val plain = PlainShelf(held, faults)
    def items: IO[List[BigInt]] = plain.items
    def put(n: BigInt): IO[Unit] = plain.put(n)

  private def tested(faults: List[Boolean]) =
    val check = Shelf.kept.checkedAgainst(
      start = (held: List[BigInt]) => (Ref[IO].of(held), Ref[IO].of(faults)).mapN(Read(_, _)),
      observe = (adapter: Read) => adapter.held.get)
    ModelTests.run(check, semantics, elaborated.theory.vocabulary)(Nil, run).unsafeRunSync()

  test("an adapter that keeps the numbers as the model does agrees with it") {
    assertEquals(tested(Nil), None)
  }

  test("an adapter's failure is the boundary's declared error, where the model does not fail") {
    tested(List(false, true)) match
      case Some(Difference.Threw(message)) => assert(message.contains("Trouble"), message)
      case other                           => fail(s"not found: $other")
  }
