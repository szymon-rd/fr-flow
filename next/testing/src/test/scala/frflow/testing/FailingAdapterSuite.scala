package frflow.testing

import cats.effect.{IO, Ref}
import cats.effect.unsafe.implicits.global
import cats.syntax.all.*
import frflow.LeanType
import frflow.core.expr.Value
import frflow.core.name.{ModelName, SymbolName}
import frflow.eval.{Faults, Raised, ScalaValue, Semantics}
import frflow.eval.flow.{PlainShelf, Shelf, Trouble, World}
import frflow.testing.model.{Difference, ModelTests, Ran, Step, Typing}

/** A failing model's operations' Scala in a model test: its failure is the model's declared error, as production
  * makes it (`Bound.failures`), so it is compared with the model as a program would see it: failing alike is no
  * difference; failing alone, or with another error, is, at the step it happens.
  */
class FailingAdapterSuite extends munit.FunSuite:
  private val elaborated = Shelf.knowledge.elaborated.fold(es => fail(es.toString), identity)
  private val semantics = Semantics(elaborated)
  private val v = elaborated.theory.vocabulary
  private val trouble = LeanType[Trouble].ty
  private val put = Step(SymbolName("put"), List(Value.Num(4)))
  private val run = List(put, Step(SymbolName("items"), Nil))
  private val down = semantics.reflect(ScalaValue(Trouble.Down), trouble)
  private val shelf = v.model(Shelf.kept.name).getOrElse(fail("no shelf"))

  private def tested(faults: List[Boolean]) =
    val impl = ModelTests.of(Shelf.kept)(
      start = (held: List[BigInt]) => (Ref[IO].of(held), Ref[IO].of(faults)).mapN(PlainShelf(_, _)),
      observe = (s: PlainShelf) => s.held)(s => (s.items, s.put))
    ModelTests.run(ModelTests.Check(shelf, impl), semantics, v, (_, _, _) => IO.unit)(ScalaValue(Nil), run)
      .unsafeRunSync()

  test("Scala that keeps the numbers as the model does agrees with it") {
    assertEquals(tested(Nil), None)
  }

  test("the Scala's failure is the model's declared error, where the model does not fail: at that step") {
    assertEquals(tested(List(true)), Some(Difference.Call(put, Ran.Failed(down), Ran.Gave(Value.Unit))))
  }

  test("Scala and model failing at one step: alike is no difference, with another error is one") {
    def against(error: Trouble) =
      val failing = new World[IO]:
        def call(op: SymbolName, args: List[ScalaValue]): IO[ScalaValue] =
          IO.raiseError(Raised(ScalaValue(error), trouble))
        def read(m: ModelName): IO[ScalaValue] = IO.raiseError(IllegalStateException("no state"))
        def write(m: ModelName, s: ScalaValue): IO[Unit] = IO.unit
      Ref.of[IO, Map[ModelName, ScalaValue]](Map(Shelf.kept.name -> ScalaValue(List.empty[BigInt]),
        Faults.model -> ScalaValue(List(true)))).flatMap(states =>
        ModelTests(failing, World.models(semantics, v, states), Typing(semantics, v)).firstDifference(List(put)))
        .unsafeRunSync()
    assertEquals(against(Trouble.Down), None)
    val tooBig = semantics.reflect(ScalaValue(Trouble.TooBig(4)), trouble)
    assertEquals(against(Trouble.TooBig(4)), Some(Difference.Call(put, Ran.Failed(tooBig), Ran.Failed(down))))
  }
