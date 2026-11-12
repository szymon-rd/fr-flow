package frflow.dsl.structure

import frflow.core.name.SymbolName
import frflow.core.ty.Ty
import frflow.dsl.lifted.NotRead
import frflow.dsl.compiled.steps.ClassSyntax.lifted
import scala.annotation.experimental

/** A structure as a Definition: its members are Definitions of their own, typed over the structure; the class that
  * implements it gives each its code, read from the method; and the model elaborates.
  */
@experimental class StructureSuite extends munit.FunSuite:
  private val till = TillModel.till
  private val structure = Ty.Data(frflow.core.name.TypeName("Till"))

  test("a structure's Definition is typed as the structure, and each member is a Definition over it") {
    assertEquals(till.leanType.ty, structure)
    assertEquals(till.members.map(m => m.name -> m.changes),
      List("take" -> true, "taken" -> false, "total" -> false, "count" -> false))
    assertEquals(till.member("take").name, SymbolName("till_take"))
    assertEquals(till.member("take").leanType.ty, Ty.FnOf(List(structure, Ty.Data(frflow.core.name.TypeName("Sale"))),
      Ty.TupleOf(List(Ty.Bool, structure))))
    assertEquals(till.member("total").leanType.ty, Ty.FnOf(List(structure), Ty.Num(frflow.core.ty.NumKind.Big)))
  }

  test("the model of a structure given the class that implements it elaborates") {
    val elaborated = TillModel.model.elaborated.fold(es => fail(es.toChain.toList.mkString("; ")), identity)
    assertEquals(elaborated.theory.nodes.map(_.node.id.value).sorted, List("noStepForgetsASale", "takenIsRecorded",
      "takenOnce", "takingAddsItsAmount"))
    assertEquals(frflow.core.analysis.Validate(elaborated).fold(_.toChain.toList.map(_.toString), _ => Nil), Nil)
  }

  test("each member is given its code, one no claim mentions too, and one that changes it among other calls") {
    val elaborated = TillModel.model.elaborated.fold(es => fail(es.toChain.toList.mkString("; ")), identity)
    assertEquals(elaborated.theory.code.attached.keySet.map(_.value),
      Set("till_take", "till_taken", "till_total", "till_count", "till_take_among"))
    val (steps, sale) = (Ty.ListOf(Ty.TupleOf(List(structure, structure))), Ty.Data(frflow.core.name.TypeName("Sale")))
    assertEquals(till.among("take").leanType.ty, Ty.FnOf(
      List(structure, Ty.MapOf(Ty.Num(frflow.core.ty.NumKind.Big), structure), sale),
      Ty.TupleOf(List(Ty.TupleOf(List(Ty.Bool, structure)), Ty.TupleOf(List(steps, steps))))))
  }

  test("a class is lifted by its type, with the word of each structure it holds: any other number is refused") {
    val refused = intercept[NotRead](lifted[Till.CashTill](TillModel.till))
    assert(refused.getMessage.contains("CashTill holds 0 structures and is given 1 words"), refused.getMessage)
    val made = compileErrors("""
      import frflow.dsl.compiled.steps.ClassSyntax.lifted
      lifted(Till.CashTill(Nil))""")
    assert(made.nonEmpty, "a class made where it is lifted is no longer read")
  }

  test("a class is read from its TASTy as the model is built: Scala the reader does not read is said with its place") {
    val refused = intercept[NotRead](lifted[Unread.Looping])
    assert(refused.getMessage.contains("Unread.scala:"), refused.getMessage)
    assert(refused.getMessage.contains("lifted code cannot hold"), refused.getMessage)
  }

  test("a trait no member changes, no `caps.Mutable`, is declared, lifted and held as any structure") {
    import PricesModel.{basket, model, pricing}
    assertEquals(pricing.members.map(m => m.name -> m.changes), List("price" -> false, "tax" -> false))
    val elaborated = model.elaborated.fold(es => fail(es.toChain.toList.mkString("; ")), identity)
    assertEquals(elaborated.theory.code.attached.keySet.map(_.value),
      Set("pricing_price", "pricing_tax", "basket_add", "basket_due", "basket_add_among", "basket_holds_pricing"))
    assertEquals(basket.member("due").leanType.ty,
      Ty.FnOf(List(Ty.Data(frflow.core.name.TypeName("Basket"))), Ty.Num(frflow.core.ty.NumKind.Big)))
    assertEquals(frflow.core.analysis.Validate(elaborated).fold(_.toChain.toList.map(_.toString), _ => Nil), Nil)
  }
