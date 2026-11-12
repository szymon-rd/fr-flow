package frflow.core.typing

import cats.data.{NonEmptyChain, Validated, ValidatedNec}
import frflow.core.Theory
import frflow.core.expr.{Binder, Expr, Exprs, Lambda}
import frflow.core.name.VarId
import frflow.core.ty.Ty
import frflow.core.vocab.Vocabulary

/** The IR's checker: every variable bound around it, at its binder's type; no two binders on one path at one
  * level; every node typed as its parts are (`Local`). What elaboration and `Resolve` build is checked by it
  * (`theory`), so a term ill-formed by a FrFlow bug fails where it is made, not in the prover.
  */
final class IrCheck(local: Local):
  /** The type of `e`, over variables bound outside it (`free`, a define's inputs), or every problem with it. */
  def apply(e: Expr, free: List[Binder] = Nil): ValidatedNec[IrError, Ty] =
    val all = errors(e, free.map(x => x.id -> x.ty).toMap)
    NonEmptyChain.fromSeq(all).fold(Validated.validNec(Exprs.typeOf(e)))(Validated.invalid)

  /** A lambda, its body over its parameters. */
  def lambda(l: Lambda): ValidatedNec[IrError, Ty] = apply(Expr.Fun(l))

  private def errors(e: Expr, scope: Map[VarId, Ty]): List[IrError] =
    val here = e match
      case Expr.Var(x) => scope.get(x.id) match
          case None                => List(IrError.Unbound(x))
          case Some(t) if t != x.ty => List(IrError.AtAnotherType(x, t))
          case _                   => Nil
      case other       => Option.unless(local.typed(other))(IrError.Mistyped(other)).toList
    val rebound = Exprs.binders(e).filter(x => scope.contains(x.id)).map(IrError.Rebound(_))
    here ++ rebound ++ inside(e, scope).flatMap((c, sc) => errors(c, sc))

  /** Each child with the variables in scope at it: a binder's body sees the binder, what it ranges over does not. */
  private def inside(e: Expr, scope: Map[VarId, Ty]): List[(Expr, Map[VarId, Ty])] =
    def under(xs: List[Binder]) = scope ++ xs.map(x => x.id -> x.ty)
    e match
      case Expr.Fun(l)                      => List(l.body -> under(l.params))
      case Expr.Quant(_, xs, b)             => List(b -> under(xs))
      case Expr.Let(x, v, b)                => List(v -> scope, b -> under(List(x)))
      case Expr.Iterate(_, on, x, b, _)     => List(on -> scope, b -> under(List(x)))
      case Expr.Fold(on, z, acc, x, b)      => List(on -> scope, z -> scope, b -> under(List(acc, x)))
      case Expr.Pairwise(on, x, y, b)       => List(on -> scope, b -> under(List(x, y)))
      case Expr.Match(on, arms, _)          => (on -> scope) :: arms.map(a => a.body -> under(a.pattern.binders))
      case other                            => Exprs.children(other).map(_ -> scope)

object IrCheck:
  def of(v: Vocabulary): IrCheck = IrCheck(Local(IrContext.of(v)))

  /** Every problem with the IR of a theory: each statement's formula, each define's lambda over its inputs. */
  def theory(t: Theory): List[IrError] =
    val check = of(t.vocabulary)
    def all(v: ValidatedNec[IrError, Ty]) = v.fold(_.iterator.toList, _ => Nil)
    val formulas = t.nodes.flatMap(_.node.statement.said).flatMap(f => all(check(f.value)))
    val defines = t.vocabulary.defines.flatMap(d => all(check.lambda(d.lambda)))
    formulas ++ defines

  /** The theory, or a FrFlow bug naming the problems with its IR. */
  def checked(t: Theory): Theory = theory(t) match
    case Nil => t
    case es  => throw IllegalStateException(s"FrFlow bug: an ill-formed IR: ${es.take(5).mkString("; ")}")
