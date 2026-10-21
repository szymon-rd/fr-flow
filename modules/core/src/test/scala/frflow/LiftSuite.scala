package frflow

import frflow.dsl.*
import frflow.fixtures.*
import frflow.ir.*
import frflow.json.Json
import frflow.lift.{Code, Schema}
import frflow.render.LeanPrinter

/** The macro lifter: Scala code in, IR and Lean out, with the Scala code still executable. */
class LiftSuite extends munit.FunSuite:

  private def lean(c: Code[?]): String = LeanPrinter.expr(c.lifted.body)

  test("case class construction, fields and copy") {
    val mk = Code((i: Item) => Item(i.name, i.qty + 1, i.tags))
    assertEquals(lean(mk), "Item.mk i.name (i.qty + 1) i.tags")
    val cp = Code((i: Item) => i.copy(qty = 0))
    assertEquals(lean(cp), "{ i with qty := 0 }")
    assertEquals(cp.value(Item("a", 3, Set.empty)), Item("a", 0, Set.empty))
  }

  test("ADT definitions carry fields, types and Scaladoc") {
    val c = Code((i: Item) => i.qty)
    val item = c.ir.defs.adts("Item")
    assertEquals(item.doc, "A stock item.")
    item.shape match
      case AdtShape.Product(fs) =>
        assertEquals(fs.map(f => f.name -> LeanPrinter.tpe(f.tpe)), List("name" -> "String", "qty" -> "Int", "tags" -> "Scala.Set String"))
        assertEquals(fs.map(_.doc), List("item name", "quantity in stock", "labels"))
      case other => fail(s"unexpected shape $other")
    assert(item.source.contains("final case class Item"), item.source)
  }

  test("methods are read from their definitions, with the receiver as `self`") {
    val c = Code((inv: Inventory) => inv.has("a"))
    assertEquals(lean(c), "Inventory.has inv \"a\"")
    val has = c.ir.defs.funs("Inventory.has")
    assertEquals(has.params.map(_.name), List("self", "name"))
    assertEquals(LeanPrinter.expr(has.body), "self.items name ≠ none")
    assertEquals(has.doc, "Whether an item is stocked.")
  }

  test("functions and values of objects") {
    val c = Code((i: Item) => Rules.ok(i))
    assertEquals(lean(c), "Rules.ok i")
    assertEquals(LeanPrinter.expr(c.ir.defs.funs("Rules.ok").body), "i.qty ≤ Rules.Limit")
    assertEquals(c.ir.defs.funs("Rules.Limit").params, Nil)
    assert(c.value(Item("a", 3, Set.empty)))
  }

  test("enums and pattern matching") {
    val c = Code((c: Color) => c match
      case Color.Red       => 1
      case Color.Custom(k) => k
      case _               => 0
    )
    assertEquals(lean(c), "match c with | Color.Red => 1 | Color.Custom k => k | _ => 0")
    assertEquals(c.value(Color.Custom(7)), 7)
    c.ir.defs.adts("Color").shape match
      case AdtShape.Sum(cs) => assertEquals(cs.map(_.name), List("Red", "Green", "Custom"))
      case other            => fail(s"unexpected shape $other")
  }

  test("collections: Map, Set, Option, List") {
    val c = Code((inv: Inventory) => inv.items.get("a").exists(i => i.tags.contains("x")))
    assertEquals(lean(c), "∃ (i : Item), (inv.items \"a\") = some i ∧ i.tags \"x\"")
    val u = Code((inv: Inventory, i: Item) => inv.copy(items = inv.items.updated(i.name, i), log = i.name :: inv.log))
    assertEquals(lean(u), "{ inv with items := Scala.Map.updated inv.items i.name i, log := i.name :: inv.log }")
    val all = Code((inv: Inventory) => inv.log.forall(n => inv.items.contains(n)))
    assertEquals(lean(all), "∀ n ∈ inv.log, inv.items n ≠ none")
    val s = Code((i: Item) => i.tags + "new" - "old")
    assertEquals(lean(s), "Scala.Set.excl (Scala.Set.incl i.tags \"new\") \"old\"")
    val e = Code((inv: Inventory) => inv.items.isEmpty && inv.log.isEmpty)
    assertEquals(lean(e), "(∀ k, inv.items k = none) ∧ (inv.log = [])")
  }

  test("specification logic: quantifiers and implication") {
    val c = Code(forall((i: Item) => i.qty >= 0 ==> Rules.ok(i)))
    assertEquals(lean(c), "∀ (i : Item), (i.qty ≥ 0) → (Rules.ok i)")
    intercept[NotExecutable](c.value)
  }

  test("parameters are renamed without capturing inner binders") {
    val c = Code((x: Int) => (s: Int) => x + s)
    assertEquals(LeanPrinter.expr(c.lifted.bodyWith(List("s"))), "fun (s_1 : Int) => s + s_1")
  }

  test("the IR survives encoding") {
    val c = Code((inv: Inventory) => inv.items.get("a").exists(i => Rules.ok(i)))
    assertEquals(IrCodec.readResult(Json.parse(IrCodec.result(c.ir).compact)), c.ir)
  }

  test("schemas translate types and their closure") {
    val s = summon[Schema[Inventory]]
    assertEquals(s.ir.tpe, Type.Named("Inventory"))
    assert(s.ir.defs.adts.contains("Item"))
  }

  test("unsupported Scala is a compile error at its position") {
    val errs = compileErrors("frflow.lift.Code((x: Int) => { var y = x; y })")
    assert(errs.contains("FrFlow: `var` is not supported"), errs)
    val io = compileErrors("frflow.lift.Code((x: Int) => println(x))")
    assert(io.contains("FrFlow:"), io)
  }

  test("translation is refused where Scala and the Lean reading would disagree") {
    val eq = compileErrors("frflow.lift.Code((o: frflow.fixtures.Odd) => o.x)")
    assert(eq.contains("overrides equals and hashCode"), eq)
    val ap = compileErrors("frflow.lift.Code((s: String) => frflow.fixtures.Trimmed(s, 1))")
    assert(ap.contains("FrFlow:") && !ap.contains("Trimmed.mk"), ap)
    assertEquals(LeanPrinter.expr(Code((s: String) => frflow.fixtures.Trimmed(s)).lifted.body), "Trimmed.mk s")
  }

  test("two Scala definitions with the same Lean name are rejected") {
    val errs = compileErrors("frflow.lift.Schema.derived[(frflow.fixtures.a.Dup, frflow.fixtures.b.Dup)]")
    assert(errs.contains("both translate to the Lean name Dup"), errs)
    object T extends Theory("Dup"):
      domain[frflow.fixtures.a.Dup]
      domain[frflow.fixtures.b.Dup]
    val err = intercept[frflow.model.ModelError](frflow.model.TheoryModel.from(Model(T)))
    assert(err.getMessage.contains("both translate to the Lean name Dup"), err.getMessage)
  }
