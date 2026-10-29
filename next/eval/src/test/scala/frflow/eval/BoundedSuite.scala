package frflow.eval

import frflow.*
import frflow.core.analysis.{Problem, Validate}
import frflow.core.name.{ModelName, NodeId}
import frflow.core.ty.Ty

/** A counter held as a Scala `Int`. */
final case class Tally(count: Int) derives LeanType

/** Nothing FrFlow asks to exist is of a type holding a Scala `Int` or `Long` (`Bounded`): not a rule of `always` over
  * one (`inhabited_`), nor a store's state holding one, nor a Definition given plain Scala (its consistency), nor a
  * value over a condition (`satisfiable_`); each refused with a pointer to BigInt. A `forall` over one, with no
  * condition, is not.
  */
class BoundedSuite extends munit.FunSuite:
  private val tally = Ty.Data(frflow.core.name.TypeName("Tally"))
  private def problems(kb: FrModel): List[Problem] =
    kb.elaborated.fold(es => fail(es.iterator.mkString), e => Validate(e).fold(_.iterator.toList, _ => Nil))
      .filter(_.productPrefix == "SaidToExist")

  private val positive = Node.claim("Every tally is itself.")(forall((t: Term[Tally]) => t === t))
  private val counted = Node.claim("A tally always counts.")(always[Tally](t => t === t))
  private val big = Definition[Tally => Boolean]("whether a tally is big")
  private val bigIsBig = Node.assumption("A tally is big exactly when it is itself.")(
    forall((t: Term[Tally]) => big(t) === (t === t)))
  private val noneOther = define { (t: Term[Tally]) => !forall((u: Term[Tally]) => u === t) }
  private val inDefine = Node.claim("A tally has another.")(forall((t: Term[Tally]) => noneOther(t)))
  private val conditioned = Node.claim("A tally equal to another is it.")(
    forall((t: Term[Tally], u: Term[Tally]) => (t === u) implies (u === t)))

  private val read = Definition[Program[Tally]]("the tally")
  object tallied extends StateModel[Tally]("a tally kept"):
    read.means(state.get)
  private val kept = Node.claim("The kept tally is itself.")(always(tallied)(t => t === t))

  test("a forall over a type holding an Int, with no condition, says nothing exists") {
    assertEquals(problems(FrModel("Tallies")(positive)), Nil)
  }

  test("a rule of always over one, a condition over one, and plain Scala of one are refused") {
    assertEquals(problems(FrModel("Tallies")(counted)),
      List(Problem.SaidToExist(tally, Problem.Place.Variable(NodeId("counted")))))
    assertEquals(problems(FrModel("Tallies")(conditioned)),
      List(Problem.SaidToExist(tally, Problem.Place.Variable(NodeId("conditioned")))))
    val tested = FrModel("Tallies")(bigIsBig).implementTested(big)(_ => (t: Tally) => t.count > 9)
    assertEquals(problems(tested), List(Problem.SaidToExist(Ty.FnOf(List(tally), Ty.Bool),
      Problem.Place.Value("big"))))
  }

  test("an exists inside a define a statement calls is refused, however the statement reads it") {
    assertEquals(problems(FrModel("Tallies")(inDefine)),
      List(Problem.SaidToExist(tally, Problem.Place.Variable(NodeId("inDefine")))))
  }

  test("a rule of always over a store's state holding one is refused, its store named") {
    assert(problems(FrModel("Tallies")(kept)).contains(Problem.SaidToExist(tally,
      Problem.Place.State(ModelName("tallied")))), problems(FrModel("Tallies")(kept)))
  }

