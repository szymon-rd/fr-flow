package frflow.eval.term

import frflow.proof.lean.ast.*
import frflow.proof.lean.lower.LowerType
import frflow.proof.lean.laws.MoreTerms

/** The programs `MoreTerms` runs, as Lean declares them, each the Lean of its Scala in `Closed.programs`: `run n`
  * gives `n + 1` and adds `n` to the store; `attempt n` fails with "negative" when `n < 0`, changing nothing, and
  * otherwise gives `n` and stores it.
  */
object LawPrograms:
  private def n(s: String): LeanName = Names.builtin(s)
  private def v(s: String): LExpr = LExpr.Name(n(s))
  private val int = v("Int")
  private val world = v("World")
  private val inputs = List(LBinder.Explicit(n("n"), int), LBinder.Explicit(n("w"), world))
  private def storing(e: LExpr): LExpr = LExpr.Update(v("w"), List(n("stored") -> e))
  private def except(side: String, e: LExpr): LExpr = LExpr.Paren(LExpr.App(LExpr.Const(Names.path("Except", side)),
    List(e)))

  private val attemptTy = LExpr.Infix(LOp.Arrow, int, LExpr.Infix(LOp.Arrow, world, LExpr.Paren(LExpr.Infix(LOp.Times,
    LExpr.App(v("Except"), List(v("String"), int)), world))))

  val decls: List[Decl] = List(
    Decl.Def(List(Attr.FrflowDefs), n("run"), Nil, LowerType.binder(MoreTerms.runTy), LExpr.Paren(LExpr.Fun(inputs,
      LExpr.Tuple(List(LExpr.Infix(LOp.Add, v("n"), LExpr.Num(1)),
        storing(LExpr.Infix(LOp.Add, LExpr.Dot(v("w"), "stored"), v("n")))))))),
    Decl.Def(List(Attr.FrflowDefs), n("attempt"), Nil, attemptTy, LExpr.Paren(LExpr.Fun(inputs,
      LExpr.If(LExpr.Infix(LOp.Lt, v("n"), LExpr.Num(0)), LExpr.Tuple(List(except("error", LExpr.Str("negative")),
        v("w"))), LExpr.Tuple(List(except("ok", v("n")), storing(v("n")))))))))
