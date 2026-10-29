package frflow.proof.lean.laws

import frflow.core.Booking
import frflow.core.expr.{LawSeeds, Terms, Tm}
import frflow.core.term.Final
import frflow.proof.layout.{LeanTag, LeanWorkspace}
import frflow.proof.lean.ast.*
import frflow.proof.lean.lower.{Naming, LowerType}
import frflow.proof.lean.print.Print
import frflow.proof.lean.term.Printed

/** Every generated term the printer's laws print is Lean that elaborates (`sbt leanTest`): each a `def` over the
  * symbols the generators name, in a module declaring the laws' types, world and define. That Lean decides each
  * term as the evaluator does waits for the evaluator (next/eval).
  */
class PrinterLeanSuite extends munit.FunSuite:
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(20, "minutes")
  private val naming = Naming.over(Set.empty, Set(Booking.name.value, MoreTerms.eventName.value, "World"))
  private val terms: List[Final[Boolean]] =
    LawSeeds(300).flatMap(seed => List(Tm.closed(Terms(seed).bool(3, 0)), MoreTerms(seed).formula))

  private def n(s: String): LeanName = Names.builtin(s)
  private def x(s: String, t: LExpr): LBinder = LBinder.Explicit(Names.ident(s), t)
  private val prop = LExpr.Name(n("Prop"))
  private val int = LExpr.Name(n("Int"))
  /** The symbols the generators name, each at its type; `attempt` a program that may fail. */
  private val symbols: List[LBinder] = List(x("p", LowerType.binder(Terms.fnTy)), x("k", int),
    x("xs", LowerType(frflow.core.ty.Ty.ListOf(frflow.core.Lang.big))),
    x("o", LowerType(frflow.core.ty.Ty.OptionOf(frflow.core.Lang.big))), x("slot", LowerType(Booking.ty)),
    x("s", LowerType(frflow.core.ty.Ty.SetOf(frflow.core.Lang.big))),
    x("m", LowerType(frflow.core.ty.Ty.MapOf(frflow.core.Lang.big, frflow.core.Lang.big))),
    x("ev", LowerType(MoreTerms.eventTy)), x("outcome", LowerType(MoreTerms.outcomeTy)),
    x("run", LowerType.binder(MoreTerms.runTy)), x("attempt", LExpr.Infix(LOp.Arrow, int, LExpr.Infix(LOp.Arrow,
      LExpr.Name(n("World")), LExpr.Paren(LExpr.Infix(LOp.Times, LExpr.App(LExpr.Name(n("Except")),
      List(LExpr.Name(n("String")), int)), LExpr.Name(n("World"))))))))

  private def types: List[Decl] = List(
    Decl.Structure(n("Booking"), Booking.data match
      case frflow.core.ty.DataType.Product(_, _, fs) => fs.map(f => Names.ident(f.name) -> LowerType(f.ty))
      case _                                         => Nil),
    Decl.Inductive(n("Event"), List(n("Booked") -> List(x("at", int)), n("Cleared") -> Nil)),
    Decl.Structure(n("World"), List(n("stored") -> int)),
    Decl.Def(List(Attr.FrflowDefs), n("positive"), Nil, LowerType.binder(Terms.fnTy),
      Printed.formula(LawsEnv.env, naming)(Terms.positive.body)))

  test("every generated term elaborates in Lean".tag(LeanTag)) {
    val defs = terms.zipWithIndex.map((t, i) =>
      Decl.Def(Nil, n(s"t_$i"), symbols, prop, Printed.formula(LawsEnv.env, naming)(t)))
    val m = LeanModule(ModuleName(Names.path("FrFlowGen", "Laws", "Terms")), List(ModuleName(Names.path("FrFlow"))),
      Preamble.generated, Names.path("Laws"), Nil, types ++ defs)
    val (built, out) = LeanWorkspace.make("laws").build(List(m))
    assert(built, out.linesIterator.take(60).mkString("\n") + "\n" + Print.module(m).linesIterator.take(80)
      .mkString("\n"))
  }
