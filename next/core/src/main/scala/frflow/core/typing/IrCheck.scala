package frflow.core.typing

import cats.data.{NonEmptyChain, Validated, ValidatedNec}
import frflow.core.Theory
import frflow.core.expr.{Binder, Expr, Exprs, Lambda, Prog, Progs}
import frflow.core.name.VarId
import frflow.core.term.interpret.ToExpr
import frflow.core.ty.Ty
import frflow.core.vocab.Vocabulary

/** The IR's checker: every variable bound around it, at its binder's type (a program's step result for the steps
  * after it only); no two binders on one path at one level; every node and step typed as its parts are (`Local`); a
  * fact about the outside only as a whole statement. What elaboration and `Resolve` build is checked by it
  * (`theory`), so a term ill-formed by a FrFlow bug fails where it is made, not in Lean.
  */
final class IrCheck(local: Local):
  /** The type of `e`, over variables bound outside it (`free`, a define's inputs), or every problem with it. */
  def apply(e: Expr, free: List[Binder] = Nil): ValidatedNec[IrError, Ty] =
    val all = e match
      case Expr.Outside(f) => Option.unless(local.fact(f))(IrError.Mistyped(e)).toList
      case _               => errors(e, free.map(x => x.id -> x.ty).toMap)
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
    val steps = e match
      case Expr.Do(p, _) => prog(p, scope)
      case _             => Nil
    here ++ rebound ++ steps ++ inside(e, scope).flatMap((c, sc) => errors(c, sc))

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
      case Expr.Do(_, _)                    => Nil // its steps in order (`prog`)
      case other                            => Exprs.children(other).map(_ -> scope)

  /** A program's steps, each over the variables bound before it: what a step binds is in scope for what follows it
    * (a loop's element and a handler's error for their bodies), and rebinds none around it.
    */
  private def prog(p: Prog[Expr], scope: Map[VarId, Ty]): List[IrError] =
    val (terms, after) = IrCheck.scoped(p)
    Option.unless(local.step(p))(IrError.MistypedStep(p)).toList ++ terms.flatMap(errors(_, scope)) ++
      after.flatMap { (xs, next) =>
        val inner = scope ++ xs.map(x => x.id -> x.ty)
        xs.filter(x => scope.contains(x.id)).map(IrError.Rebound(_)) ++ (next match
          case e: Expr                  => errors(e, inner)
          case q: Prog[Expr] @unchecked => prog(q, inner))
      }

object IrCheck:
  /** A concurrent pair's result, as its sequential reading gives it. */
  private def pair(a: Binder, b: Binder): Expr = summon[Prog.Pairs[Expr]].pair(a, b)

  def of(v: Vocabulary): IrCheck = IrCheck(Local(IrContext.of(v)))

  /** Every problem with the IR of a theory: each statement's formula, each define's lambda over its inputs, each
    * model operation's steps over its parameters.
    */
  def theory(t: Theory): List[IrError] =
    val check = of(t.vocabulary)
    def all(v: ValidatedNec[IrError, Ty]) = v.fold(_.iterator.toList, _ => Nil)
    val formulas = t.nodes.flatMap(_.node.statement.said).flatMap(f => all(check(f.value)))
    val defines = t.vocabulary.defines.flatMap(d => all(check.lambda(d.lambda)))
    val ops = t.vocabulary.models.flatMap(_.ops).flatMap(o => all(check.lambda(Lambda(o.params,
      Expr.Do(Progs.map(o.steps)(s => ToExpr.of(s.run, o.params.size)), Ty.FlowOf(o.result, None)),
      Ty.FlowOf(o.result, None)))))
    formulas ++ defines ++ ops

  /** A step's own terms, over what is bound before it; and what follows it, each with the variables bound for it. */
  private def scoped(p: Prog[Expr]): (List[Expr], List[(List[Binder], Expr | Prog[Expr])]) = p match
    case Prog.Pure(t)                     => (List(t), Nil)
    case Prog.Call(_, as, _)              => (as, Nil)
    case Prog.Bind(a, x, r)               => (Nil, List(Nil -> a, List(x) -> r))
    case Prog.Let(x, v, r)                => (List(v), List(List(x) -> r))
    case Prog.Loop(o, x, b)               => (List(o), List(List(x) -> b))
    case Prog.Collect(o, x, b)            => (List(o), List(List(x) -> b))
    case Prog.ParEach(o, x, b, _)         => (List(o), List(List(x) -> b))
    case Prog.Accumulate(o, z, acc, x, b) => (List(o, z), List(List(acc, x) -> b))
    case Prog.Branch(c, a, b)             => (List(c), List(Nil -> a, Nil -> b))
    case Prog.Read(_)                     => (Nil, Nil)
    case Prog.Write(_, s)                 => (List(s), Nil)
    case Prog.Modify(_, x, n)             => (Nil, List(List(x) -> n))
    case Prog.Raise(e)                    => (List(e), Nil)
    case Prog.Catch(b, _, x, h)           => (Nil, List(Nil -> b, List(x) -> h))
    case Prog.Par(l, a, r, b)             => (Nil, List(Nil -> l, Nil -> r, List(a, b) -> pair(a, b)))
    case Prog.Race(l, r, reading)         => (Nil, List(l, r, reading).map(Nil -> _))
    case Prog.Guard(b, _, f, reading)     => (Nil, List(b, f, reading).map(Nil -> _))
    case Prog.Atomic(b)                   => (Nil, List(Nil -> b))

  /** The theory, or a FrFlow bug naming the problems with its IR. */
  def checked(t: Theory): Theory = theory(t) match
    case Nil => t
    case es  => throw IllegalStateException(s"FrFlow bug: an ill-formed IR: ${es.take(5).mkString("; ")}")
