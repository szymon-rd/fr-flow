package frflow.proof.layout

import frflow.core.{Kb, Lang}
import frflow.core.Nodes.*
import frflow.core.analysis.{Resolve, Resolved, Validate}
import frflow.core.expr.Value
import frflow.core.name.NodeId
import frflow.core.term.{Bound, Stated, Sym}
import frflow.core.ty.Ty
import frflow.proof.lean.ast.LeanModule
import frflow.proof.lean.print.Print
import frflow.proof.obligation.Constant
import frflow.proof.terms.TermTable

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

/** A step that does not hold: `small` (`f n` exactly when `n < 5`) from a part fixing `f` to `n < 3`; refuted at 4. */
object Refuted:
  private val test = Ty.FnOf(List(Lang.big), Ty.Bool)
  private def below(name: String, k: Int) = claim(name)(Lang.formula([T[_]] => (l: Lang[T]) =>
    l.forall[BigInt]("n", Lang.big)(n => l.s.eq(l.call(l.sym[BigInt => Boolean]("f", test), n), l.s.lt(n, l.num(k))))))
  val resolved: Resolved = Resolve(Validate(Kb.of(below("small", 5), below("fixed", 3)).naming(declaration("f", test))
    .linking(partOf("fixed", "small")).elaborated).fold(ps => throw IllegalStateException(ps.toString), identity))
  val table: TermTable = TermTable.of(resolved)
  val found: Refutation = Refutation(Stated([T[_]] => (s: Sym[T]) =>
    s.lam(Bound[BigInt]("n", Lang.big))(n => s.lt(n, Lang(s).num(3)))), test, List(Constant(Value.Num(4), Lang.big)))
  val laid: Laid = Laid(resolved, Map.empty, Nil)
  def modules: List[LeanModule] = laid.modules :+ RefutesModule.of(resolved, table, NodeId("small"), found)

/** The refutation built by Lean: Lean proves `complete` false on the case. */
class RefutedLeanSuite extends munit.FunSuite:
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(20, "minutes")
  test("refuted: Lean proves the step false on the case".tag(LeanTag)) {
    val out = LeanWorkspace.make("refuted").build(Refuted.modules)._2
    val refutes = Refuted.modules.last
    val e = frflow.proof.reading.Elaboration(Print.module(refutes), out, refutes.name.file.value.stripPrefix("lean/"))
    assert(out.linesIterator.exists(l => l.contains(s" ${refutes.name.dotted} ") && !l.startsWith("✖")), out)
    assertEquals(e.verdict("refutes"), frflow.proof.reading.TheoremVerdict.Proven, out)
  }
