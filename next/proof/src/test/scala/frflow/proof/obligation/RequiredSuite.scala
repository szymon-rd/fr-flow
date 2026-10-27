package frflow.proof.obligation

import frflow.core.{Kb, Lang}
import frflow.core.Nodes.*
import frflow.core.analysis.{Resolve, Resolved, Validate}
import frflow.core.name.NodeId
import frflow.core.ty.Ty
import frflow.proof.layout.{Mini, Programs, ProgramsProject}
import frflow.proof.lean.print.Print
import frflow.proof.terms.TermTable

/** One test per rule of what must hold of a node (`Required`): `complete`, `feasible`, `impl`, `cover_<op>`, `made_`
  * of a define, of a program and of a store's operation, and `commute_i` of a pair and of a traverse at once.
  */
class RequiredSuite extends munit.FunSuite:
  private def names(r: Resolved, n: String, authored: Set[(NodeId, ObligationName)] = Set.empty) =
    Required.of(r, authored, NodeId(n)).map(o => o.name -> o.discharge)
  private val (allowsOne, complete) = (NodeId("allowsOne"), ObligationName.Complete)

  test("complete: a node with parts and no proven code, made by its parts") {
    assertEquals(names(Mini.resolved, "allowsOne"), List(complete -> Discharge.Auto))
    assertEquals(Required.complete(Mini.resolved, allowsOne), Some(Prop.over(List(allowsOne),
      Prop.Implies(List(Hyp.of(NodeId("allowedPositive"))), Prop.claim(allowsOne)))))
  }

  test("feasible: asked of an authored complete only when what is below it is not witnessed, or authored itself") {
    val authored = Set(allowsOne -> complete)
    assertEquals(names(Mini.resolved, "allowsOne", authored), List(complete -> Discharge.Authored))
    assertEquals(names(Mini.resolved, "allowsOne", authored + (allowsOne -> ObligationName.Feasible)),
      List(complete -> Discharge.Authored, ObligationName.Feasible -> Discharge.Authored))
    val r = Unwitnessed.resolved
    val feasible = Required.of(r, Set(allowsOne -> complete), allowsOne).filter(_.name == ObligationName.Feasible)
    assertEquals(feasible.map(_.goal), List(Prop.Exists(List(allowsOne, NodeId("grows")),
      Prop.Both(cats.data.NonEmptyList.one(Prop.claim(NodeId("grows")))))))
    assertEquals(feasible.map(_.discharge), List(Discharge.Auto))
  }

  test("impl: a node about a Definition with proven code, from what its code relies on") {
    assertEquals(names(Mini.resolved, "bookRuns"), List(ObligationName.Impl -> Discharge.Auto))
    assertEquals(names(Programs.resolved, "fetchRuns").map(_._1), List(ObligationName.Impl))
  }

  test("cover_: an always kept by each program writing a store it is about, and by no other program") {
    assertEquals(names(Mini.resolved, "endsAfterStart").map(_._1), List(ObligationName.Cover("book")))
    assert(!names(Programs.resolved, "endsAfterStart").exists(_._1.isInstanceOf[ObligationName.Cover]))
  }

  test("made_: of a define making what the always is about, and of a program whose run gives one") {
    assertEquals(names(Programs.resolved, "endsAfterStart").map(_._1),
      List(ObligationName.Made("reschedule"), ObligationName.Made("fetch"), ObligationName.Made("sample")))
    val made = Required.made(Programs.resolved, NodeId("endsAfterStart"))
    assertEquals(made.map(_.doc).take(2), List("Every result of later meets endsAfterStart.",
      "Every result of a run of fetchOne_run meets endsAfterStart."))
  }

  test("made_ of a store's operation: on its model, over a world meeting what always holds") {
    val made = Required.made(Programs.resolved, NodeId("endsAfterStart")).filter(_.name == ObligationName.Made("sample"))
    assertEquals(made.map(o => (o.goal, o.doc)), List((Prop.over(Nil, Prop.Makes(NodeId("endsAfterStart"),
      frflow.core.name.SymbolName("sample"), made.head.goal match
        case Prop.Forall(_, m: Prop.Makes) => m.formula
        case _                              => fail("not a maker's statement"),
      Map(frflow.core.name.SymbolName("sample") -> Substitute.Code(frflow.core.name.DefName("Shelved.sample_of"))))),
      "Every result of shelved's sample meets endsAfterStart, on a world meeting what always holds.")))
    assertEquals(Required.made(Mini.resolved, NodeId("endsAfterStart")), Nil) // `add` gives no booking
  }

  test("commute_: a pair at once and a traverse at once, each in either order") {
    def commutes(n: String) = Required.commutes(Programs.resolved, NodeId(n))
    assertEquals(commutes("pairRuns").map(_.name), List(ObligationName.Commute(0)))
    assertEquals(commutes("eachRuns").map(_.name), List(ObligationName.Commute(0)))
    assertEquals(commutes("fetchRuns"), Nil)
    val each = commutes("eachRuns").head.goal match
      case Prop.Forall(_, Prop.Commutes(c, _)) => c
      case other                                => fail(s"not a commutation: $other")
    assertEquals((each.apart.map(a => (a.one.hint, a.two.hint)), each.result),
      (Some(("x_one", "x_two")), Ty.TupleOf(List(Lang.big, Lang.big))))
  }

  test("commute_ in Lean: both orders run on the models from every world") {
    val spec = ProgramsProject.modules.find(_.name.dotted == "FrFlowGen.Test.pairRuns.Spec").map(Print.module)
    val expected = """@[frflow_defs] def commute_0 : Prop :=
      |  ∀ (n : Int) (w : World), FrFlow.runOn ((do
      |        let a ← pure n
      |        let c ← pure (n + 1)
      |        pure (a, c)) : StateM World (Int × Int)) w = FrFlow.runOn ((do
      |        let c ← pure (n + 1)
      |        let a ← pure n
      |        pure (a, c)) : StateM World (Int × Int)) w""".stripMargin
    assert(spec.exists(_.contains(expected)), spec.getOrElse("no module"))
  }

  test("the table of open terms the rules apply declarations to") {
    assertEquals(TermTable.of(Mini.resolved).claims(allowsOne).symbols.map(_.value), List("allowed"))
  }

/** `allowsOne` from a part no equation solves: its group of consistency is not witnessed. */
object Unwitnessed:
  private val test = Ty.FnOf(List(Lang.big), Ty.Bool)
  private def allowed[T[_]](l: Lang[T], n: T[BigInt]): T[Boolean] =
    l.call(l.sym[BigInt => Boolean]("allowed", test), n)
  val resolved: Resolved = Resolve(Validate(Kb.of(
    claim("allowsOne")(Lang.formula([T[_]] => (l: Lang[T]) => allowed(l, l.num(1)))),
    claim("grows")(Lang.formula([T[_]] => (l: Lang[T]) => l.forall[BigInt]("n", Lang.big)(n =>
      l.s.implies(allowed(l, n), allowed(l, l.s.add(n, l.num(1))))))))
    .naming(declaration("allowed", test)).linking(partOf("grows", "allowsOne")).elaborated)
    .fold(ps => throw IllegalStateException(ps.toString), identity))
