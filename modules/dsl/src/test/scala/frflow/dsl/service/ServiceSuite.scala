package frflow.dsl.service

import frflow.core.name.SymbolName
import frflow.core.ty.Ty
import scala.annotation.experimental

/** A service as a Definition: its members are Definitions of their own, typed over the service; the class that
  * implements it gives each its code, read from the method; and the model elaborates.
  */
@experimental class ServiceSuite extends munit.FunSuite:
  private val till = TillModel.till
  private val service = Ty.Data(frflow.core.name.TypeName("Till"))

  test("a service's Definition is typed as the service, and each member is a Definition over it") {
    assertEquals(till.leanType.ty, service)
    assertEquals(till.members.map(m => m.name -> m.changes),
      List("take" -> true, "taken" -> false, "total" -> false, "count" -> false))
    assertEquals(till.member("take").name, SymbolName("till_take"))
    assertEquals(till.member("take").leanType.ty, Ty.FnOf(List(service, Ty.Data(frflow.core.name.TypeName("Sale"))),
      Ty.TupleOf(List(Ty.Bool, service))))
    assertEquals(till.member("total").leanType.ty, Ty.FnOf(List(service), Ty.Num(frflow.core.ty.NumKind.Big)))
  }

  test("the model of a service given the class that implements it elaborates") {
    val elaborated = TillModel.model.elaborated.fold(es => fail(es.toChain.toList.mkString("; ")), identity)
    assertEquals(elaborated.theory.nodes.map(_.node.id.value).sorted, List("noStepForgetsASale", "takenIsRecorded",
      "takenOnce", "takingAddsItsAmount"))
    assertEquals(frflow.core.analysis.Validate(elaborated).fold(_.toChain.toList.map(_.toString), _ => Nil), Nil)
  }

  test("each member is given its code, one no claim mentions too, and one that changes it among other calls") {
    val elaborated = TillModel.model.elaborated.fold(es => fail(es.toChain.toList.mkString("; ")), identity)
    assertEquals(elaborated.theory.code.attached.keySet.map(_.value),
      Set("till_take", "till_taken", "till_total", "till_count", "till_take_among"))
    val steps = Ty.ListOf(Ty.TupleOf(List(service, service)))
    assertEquals(till.among("take").leanType.ty, Ty.FnOf(
      List(service, Ty.MapOf(Ty.Num(frflow.core.ty.NumKind.Big), service), Ty.Data(frflow.core.name.TypeName("Sale"))),
      Ty.TupleOf(List(Ty.TupleOf(List(Ty.Bool, service)), Ty.TupleOf(List(steps, steps))))))
  }

  test("a class is lifted by its type, with the word of each service it holds: any other number is refused") {
    val errors = compileErrors("""
      import frflow.dsl.lifted.steps.StepSyntax.lifted
      lifted[Till.CashTill](TillModel.till)""")
    assert(errors.contains("CashTill holds 0 services and is given 1 words"), errors)
    val made = compileErrors("""
      import frflow.dsl.lifted.steps.StepSyntax.lifted
      lifted(Till.CashTill(Nil))""")
    assert(made.nonEmpty, "a class made where it is lifted is no longer read")
  }
