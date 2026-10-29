package frflow.core.typing

import cats.data.{NonEmptyChain, Validated, ValidatedNec}
import frflow.core.Theory
import frflow.core.expr.{Binder, Expr, Exprs, Lambda, Prog, Progs}
import frflow.core.name.VarId
import frflow.core.ty.Ty
import frflow.core.vocab.Vocabulary

/** The IR's checker: every variable bound around it, at its binder's type; no two binders on one path at one level;
  * every node typed as its parts are (`Local`). What elaboration and `Resolve` build is checked by it (`theory`),
  * so a term ill-formed by a FrFlow bug fails where it is made, not in Lean.
  */
final class IrCheck(local: Local):
  /** The type of `e`, over variables bound outside it (`free`, a define's inputs), or every problem with it. */
  def apply(e: Expr, free: List[Binder] = Nil): ValidatedNec[IrError, Ty] =
    NonEmptyChain.fromSeq(errors(e, free.map(x => x.id -> x.ty).toMap)).fold(Validated.validNec(Exprs.typeOf(e)))(
      Validated.invalid)

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
      case Expr.Runs(r, w, _, o, a, b)      => List(r -> scope, w -> scope, b -> under(List(o, a)))
      case Expr.Do(p, _)                    => Progs.terms(p).map(_ -> under(IrCheck.steps(p)))
      case other                            => Exprs.children(other).map(_ -> scope)

object IrCheck:
  def of(v: Vocabulary): IrCheck = IrCheck(Local(v.dataType, d => v.define(d).map(defined =>
    defined.lambda.params match
      case Nil => defined.lambda.result
      case ps  => Ty.FnOf(ps.map(_.ty), defined.lambda.result))))

  /** Every problem with the IR of a theory: each statement's formula and each define's lambda over its inputs. */
  def theory(t: Theory): List[IrError] =
    val check = of(t.vocabulary)
    val formulas = t.nodes.flatMap(_.node.statement.said).flatMap(f => check(f.value).fold(_.iterator.toList, _ => Nil))
    val defines = t.vocabulary.defines.flatMap(d => check.lambda(d.lambda).fold(_.iterator.toList, _ => Nil))
    formulas ++ defines

  /** The theory, or a FrFlow bug naming the problems with its IR. */
  def checked(t: Theory): Theory = theory(t) match
    case Nil => t
    case es  => throw IllegalStateException(s"FrFlow bug: an ill-formed IR: ${es.take(5).mkString("; ")}")

  /** The variables a program's steps bind: each step's result, a loop's element, a handler's error. */
  private def steps(p: Prog[Expr]): List[Binder] = Progs.all(p).flatMap {
    case Prog.Bind(_, x, _)              => List(x)
    case Prog.Let(x, _, _)               => List(x)
    case Prog.Loop(_, x, _)              => List(x)
    case Prog.Collect(_, x, _)           => List(x)
    case Prog.Accumulate(_, _, acc, x, _) => List(acc, x)
    case Prog.Modify(_, x, _)            => List(x)
    case Prog.Catch(_, _, x, _)          => List(x)
    case Prog.Par(_, a, _, b)            => List(a, b)
    case Prog.ParEach(_, x, _, _)        => List(x)
    case _                               => Nil
  }
