package frflow.proof.layout

import frflow.proof.lean.ast.*

/** The names a statement binds, in order, for a proof `fun` over it: each `∀`'s binders, then a name from `hyps` for
  * each hypothesis stated by an arrow.
  */
object Params:
  def of(e: LExpr, hyps: List[String]): List[LeanName] = e match
    case LExpr.Forall(bs, body)                          => bs.flatMap(names) ++ of(body, hyps)
    case LExpr.Paren(inner)                              => of(inner, hyps)
    case LExpr.Infix(LOp.Arrow, _, rest) if hyps.nonEmpty => Names.builtin(hyps.head) :: of(rest, hyps.tail)
    case _                                               => Nil

  /** `fun x₁ … => body`, or the body alone over no names. */
  def lambda(names: List[LeanName], body: LExpr): LExpr =
    if names.isEmpty then body else LExpr.Fun(names.map(LBinder.Bare(_)), body)

  private def names(b: LBinder): List[LeanName] = b match
    case LBinder.Explicit(n, _) => List(n)
    case LBinder.Several(ns, _) => ns
    case LBinder.Implicit(n, _) => List(n)
    case LBinder.Bare(n)        => List(n)
    case LBinder.Member(n, _)   => List(n)
    case LBinder.Instance(_)    => Nil
