package frflow.proof.audit

import frflow.proof.lean.ast.*

/** What generated Lean says, read off its syntax alone: a module's declarations (namespaces, documentation and
  * budgets opened), the propositions each states, and the constants applied where a statement assumes them.
  */
private[audit] object Assumed:
  /** The names of the `def`s the modules declare. */
  def defs(modules: List[LeanModule]): List[String] =
    modules.flatMap(_.decls).flatMap(flat).collect { case Decl.Def(_, n, _, _, _) => n.text }

  /** The constants the modules' statements assume, each as its dotted path. */
  def taken(modules: List[LeanModule]): List[List[LeanName]] =
    modules.flatMap(_.decls).flatMap(flat).flatMap(statements).flatMap(assumed(_, negative = false))

  private def flat(d: Decl): List[Decl] = d match
    case Decl.Documented(_, x)  => flat(x)
    case Decl.Namespace(_, ds)  => ds.flatMap(flat)
    case Decl.Budgeted(_, x)    => flat(x)
    case other                  => List(other)

  private def statements(d: Decl): List[LExpr] = d match
    case Decl.Def(_, _, ps, ty, body)    => hypotheses(ps) ++ List(ty, body)
    case Decl.Theorem(_, _, ps, s, _, _) => hypotheses(ps) :+ s
    case _                               => Nil

  /** A declaration's parameters that are hypotheses, each read as assumed (as the left of `→`). */
  private def hypotheses(ps: List[LBinder]): List[LExpr] = ps.collect { case LBinder.Explicit(_, t) =>
    LExpr.Infix(LOp.Arrow, t, LExpr.Name(Names.builtin("True"))) }

  /** The constants applied where `e` assumes them: left of `→`, a hypothesis binder's type, under a `¬` turned. */
  private def assumed(e: LExpr, negative: Boolean): List[List[LeanName]] = e match
    case LExpr.Const(p) if negative               => List(p)
    case LExpr.App(f, as)                          => (f :: as).flatMap(assumed(_, negative))
    case LExpr.Infix(LOp.Arrow, a, b)              => assumed(a, !negative) ++ assumed(b, negative)
    case LExpr.Infix(_, a, b)                      => assumed(a, negative) ++ assumed(b, negative)
    case LExpr.Prefix(_, a)                        => assumed(a, !negative)
    case LExpr.Paren(i)                            => assumed(i, negative)
    case LExpr.Forall(ps, b)                       => ps.flatMap(binder(_, !negative)) ++ assumed(b, negative)
    case LExpr.Exists(ps, b)                       => ps.flatMap(binder(_, negative)) ++ assumed(b, negative)
    case LExpr.Fun(_, b)                           => assumed(b, negative)
    case LExpr.Match(on, arms)                     =>
      assumed(on, negative) ++ arms.flatMap(a => assumed(a._2, negative))
    case LExpr.If(c, a, b)                         => assumed(c, true) ++ assumed(c, false) ++ assumed(a, negative) ++
        assumed(b, negative)
    case LExpr.Let(_, _, v, b)                     => assumed(v, negative) ++ assumed(b, negative)
    case LExpr.Typed(x, _)                         => assumed(x, negative)
    case _                                         => Nil

  private def binder(b: LBinder, negative: Boolean): List[List[LeanName]] = b match
    case LBinder.Explicit(_, t) => assumed(t, negative)
    case LBinder.Member(_, in)  => assumed(in, negative)
    case _                      => Nil
