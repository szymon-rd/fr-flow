package frflow.testing

import cats.Id
import cats.effect.{IO, Ref}
import cats.effect.unsafe.implicits.global
import cats.syntax.all.*
import frflow.LeanType
import frflow.core.expr.Value
import frflow.core.name.{ModelName, OpName}
import frflow.eval.{Faults, Raised, ScalaValue, Semantics}
import frflow.eval.flow.{PlainShelf, Shelf, Trouble, World}
import frflow.testing.model.{Difference, ModelTests, Ran, Step, Typing}

/** A failing boundary's adapter in a model test: its failure is the boundary's declared error, as production's
  * `lifted` makes it (`BoundaryOps.failures`), so it is compared with the model as a program would see it: failing
  * alike is no difference; failing alone, or with another error, is, at the step it happens.
  */
class FailingAdapterSuite extends munit.FunSuite:
  private val elaborated = Shelf.knowledge.elaborated.fold(es => fail(es.toString), identity)
  private val semantics = Semantics(elaborated)
  private val v = elaborated.theory.vocabulary
  private val trouble = LeanType[Trouble].ty
  private val put = Step(Shelf.shelf.name, OpName("put"), List(Value.Num(4)))
  private val run = List(put, Step(Shelf.shelf.name, OpName("items"), Nil))
  private val down = semantics.reflect(ScalaValue(Trouble.Down), trouble)

  /** The plain shelf, its numbers read back. */
  private final class Read(val held: Ref[IO, List[BigInt]], faults: Ref[IO, List[Boolean]]) extends Shelf[IO, Id]:
    private val plain = PlainShelf(held, faults)
    def items: IO[List[BigInt]] = plain.items
    def put(n: BigInt): IO[Unit] = plain.put(n)

  private def tested(faults: List[Boolean]) =
    val check = Shelf.kept.checkedAgainst(
      start = (held: List[BigInt]) => (Ref[IO].of(held), Ref[IO].of(faults)).mapN(Read(_, _)),
      observe = (adapter: Read) => adapter.held.get)
    ModelTests.run(check, semantics, v, (_, _, _) => IO.unit)(Nil, run).unsafeRunSync()

  test("an adapter that keeps the numbers as the model does agrees with it") {
    assertEquals(tested(Nil), None)
  }

  test("an adapter's failure is the boundary's declared error, where the model does not fail: at that step") {
    assertEquals(tested(List(true)), Some(Difference.Call(put, Ran.Failed(down), Ran.Gave(Value.Unit))))
  }

  test("adapter and model failing at one step: alike is no difference, with another error is one") {
    def against(error: Trouble) =
      val adapters = new World[IO]:
        def call(b: frflow.core.name.BoundaryName, op: OpName, args: List[ScalaValue]): IO[ScalaValue] =
          IO.raiseError(Raised(ScalaValue(error), trouble))
        def read(m: ModelName): IO[ScalaValue] = IO.raiseError(IllegalStateException("no state"))
        def write(m: ModelName, s: ScalaValue): IO[Unit] = IO.unit
      Ref.of[IO, Map[ModelName, ScalaValue]](Map(Shelf.kept.name -> ScalaValue(List.empty[BigInt]),
        Faults.model -> ScalaValue(List(true)))).flatMap(states =>
        ModelTests(adapters, World.models(semantics, v, states), Typing(semantics, v)).firstDifference(List(put)))
        .unsafeRunSync()
    assertEquals(against(Trouble.Down), None)
    val tooBig = semantics.reflect(ScalaValue(Trouble.TooBig(4)), trouble)
    assertEquals(against(Trouble.TooBig(4)), Some(Difference.Call(put, Ran.Failed(tooBig), Ran.Failed(down))))
  }
