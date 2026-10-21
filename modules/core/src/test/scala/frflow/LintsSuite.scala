package frflow

import frflow.lint.{Lints, Severity}
import frflow.model.*

class LintsSuite extends munit.FunSuite:
  private val theory = CounterTheory.model

  private def codes(t: TheoryModel): Set[String] = Lints.run(t).map(_.code).toSet
  private def errorCodes(t: TheoryModel): Set[String] = Lints.errors(Lints.run(t)).map(_.code).toSet

  private def mapNode(id: String)(f: Node => Node): TheoryModel =
    theory.copy(nodes = theory.nodes.map(n => if n.id == id then f(n) else n))

  private def mapEvent(nodeId: String, ev: String)(f: EventDef => EventDef): TheoryModel =
    mapNode(nodeId)(n => n.copy(spec = n.spec.copy(events = n.spec.events.map(e => if e.name == ev then f(e) else e))))

  test("the fixture theory has no errors") {
    assertEquals(errorCodes(theory), Set.empty[String])
  }

  test("every event of a refining node must say what it refines") {
    assert(errorCodes(mapEvent("C1", "audit")(_.copy(target = EventTarget.Unspecified)))("FR044"))
  }

  test("refining an unknown parent event is an error") {
    assert(errorCodes(mapEvent("C1", "inc")(_.copy(target = EventTarget.Refines("decrement", LeanExpr("{}")))))("FR045"))
  }

  test("assume clauses must cite a declared assumption") {
    assert(errorCodes(mapEvent("C1", "inc")(e => e.copy(assumes = Seq(AssumeClause("E9", LeanExpr("True"))))))("FR042"))
  }

  test("statements are bounded") {
    val long = "This is a sentence. " * 4
    assert(errorCodes(mapNode("C0")(_.copy(statement = long)))("FR023"))
  }

  test("renderer-reserved names are rejected") {
    assert(errorCodes(mapEvent("C0", "reset")(_.copy(name = "machine")))("FR035"))
  }

  test("abstract events no concrete event refines are reported") {
    val t = mapNode("C1")(n => n.copy(spec = n.spec.copy(events = n.spec.events.filterNot(_.name == "reset"))))
    val issue = Lints.run(t).find(_.code == "FR047").get
    assertEquals(issue.severity, Severity.Warning)
  }

  test("a second root is an error") {
    val extra = theory.nodeOrFail("C0").copy(id = "C9")
    assert(errorCodes(theory.copy(nodes = theory.nodes :+ extra))("FR003"))
    assert(!codes(theory)("FR003"))
  }
