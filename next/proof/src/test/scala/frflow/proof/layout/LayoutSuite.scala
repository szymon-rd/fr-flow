package frflow.proof.layout

import frflow.core.name.NodeId
import frflow.proof.lean.ast.LeanModule
import frflow.proof.lean.print.Print

/** Where each module goes and what it imports (read off what it names), how `holds` and `root_impl` are composed
  * by name, and a step refuted on a case.
  */
class LayoutSuite extends munit.FunSuite:
  private def named(ms: List[LeanModule]): List[String] = names(ms.map(_.name))
  private def names(ms: List[frflow.proof.lean.ast.ModuleName]): List[String] =
    ms.map(_.dotted.stripPrefix("FrFlowGen.Test."))
  private def module(name: String): LeanModule =
    MiniProject.modules.find(_.name.dotted == s"FrFlowGen.Test.$name").getOrElse(fail(s"no module $name"))

  test("every module of a knowledge base, the vocabulary's first") {
    assertEquals(named(MiniProject.modules).take(7), List("Types", "Boundaries", "Domain.Def_bookIfFree",
      "Domain.Def_bookIfFree_run", "Domain.Def_endsAfterStart", "Domain.Def_startsEmpty", "Domain"))
    assertEquals(named(MiniProject.modules).filter(_.startsWith("allowsOne")),
      List("allowsOne.Spec", "allowsOne.Auto", "allowsOne.Theorems", "allowsOne.Checks"))
    assertEquals(named(MiniProject.modules).filter(_.startsWith("bookRuns")),
      List("bookRuns.Spec", "bookRuns.Impl", "bookRuns.Checks"))
    assert(Set("RootImpl", "Whole", "Whole.Checks").subsetOf(named(MiniProject.modules).toSet))
  }

  test("imports: what each module names, the domain's types always") {
    assertEquals(names(module("bookRuns.Spec").imports),
      List("Types", "Boundaries", "Domain.Def_bookIfFree_run"))
    assertEquals(names(module("allowsOne.Theorems").imports), List("Types", "allowedPositive.Spec", "allowsOne.Spec",
      "allowsOne.Auto"))
    assertEquals(names(module("RootImpl").imports), List("Types", "bookRuns.Spec", "Domain.Def_bookIfFree_run",
      "bookRuns.Impl"))
  }

  test("holds: complete applied by name to the node's open terms and its parts' proofs") {
    assert(Print.module(module("allowsOne.Theorems")).contains("""theorem holds : ∀ (allowed : Int → Prop), """ +
      """∀ (h_allowedPositive : (Test.allowedPositive.claim allowed)), (Test.allowsOne.claim allowed) :=
      |  fun allowed h_allowedPositive => (Test.allowsOne.Auto.complete (allowed := allowed) """.stripMargin +
      "(h_allowedPositive := h_allowedPositive))"))
  }

  test("root_impl: each root of proven code, from what it trusts") {
    assert(Print.module(module("RootImpl")).contains(
      "theorem root_impl : (Test.bookRuns.claim Test.bookIfFree_run) :=\n  (Test.bookRuns.Impl.impl)"))
  }

  test("a step refuted: complete false on an answer its part allows and a case") {
    val m = RefutesModule.of(Refuted.resolved, Refuted.table, NodeId("small"), Refuted.found)
    val text = Print.module(m)
    assert(text.contains("@[frflow_defs] def answer : Int → Prop :=\n  (fun (n : Int) => (n < (3 : Int)))"), text)
    assert(text.contains("@[frflow_defs] def case_0 : Int :=\n  4"), text)
    assert(text.contains("theorem refutes : ¬ Obl.complete := by"), text)
    assertEquals(names(m.imports), List("Types", "small.Spec"))
  }
