package frflow.eval.agree

import frflow.*
import frflow.core.analysis.Validate
import frflow.eval.run.OnCode
import scala.annotation.experimental
import scala.concurrent.duration.*
import whole.Tested

/** The code FrFlow reads from a class gives what the class gives on the JVM. `AgreeExamples` is that: each of its
  * examples a member run on drawn inputs, held on the terms compiled from the TASTy to what the class gave (the
  * examples run as tests themselves). Here: the model they are of is valid, and a result the class does not give
  * is not held. `AgreeRocqSuite` holds the Rocq generated from the terms to the same.
  */
@experimental class AgreeSuite extends munit.FunSuite:
  override val munitTimeout: Duration = 3.minutes

  test("the model of the classes is valid") {
    val elaborated = AgreeModel.model.elaborated.fold(es => fail(es.toChain.toList.mkString("; ")), identity)
    assertEquals(Validate(elaborated).fold(_.toChain.toList.map(_.toString), _ => Nil), Nil)
  }

  test("a result the class does not give is not held: the code read is run, not taken at its word") {
    assertEquals(Tested.onCode(AgreeSuite.Wrong()), List(OnCode.Fails, OnCode.Fails))
  }

@experimental object AgreeSuite:
  /** What the classes do not give: a sum off by one, and a journal that took a parcel it has no room for. */
  class Wrong extends FrFlowExamples(AgreeModel.model):
    import AgreeModel.{arith, journal}
    import Parcels.{Parcel, Zone}
    private val sums = Pure.PlainArith(BigInt(5))
    example("a sum off by one"):
      arith.blend(BigInt(7), BigInt(2)).in(arith.holding(sums)) is sums.blend(BigInt(7), BigInt(2)) + 1
    example("a parcel over the weight, taken"):
      val heavy = Parcel("oak", BigInt(9), Zone.Local, false)
      journal.accept(heavy).in(journal.holding(Stateful.ListJournal(BigInt(5), Nil, BigInt(0)))).result
