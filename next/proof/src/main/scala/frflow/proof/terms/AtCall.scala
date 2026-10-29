package frflow.proof.terms

import frflow.core.expr.Binder
import frflow.core.name.VarId
import frflow.core.term.{Bound, Sym}
import frflow.core.term.interpret.Guard
import frflow.core.ty.Ty

/** A call proven code makes of a Definition given plain Scala (owner §37): its arguments' types, and what it states of
  * them given a rule, on the path to it (`stated`: the rule's guard of each argument it reaches, below each condition
  * and quantifier on the way).
  */
final case class AtCall[T[_]](tys: List[Ty], stated: Guard => T[Boolean])

object AtCall:
  /** A call of these arguments: the rule of each one it reaches, all of them. */
  def of[T[_]](s: Sym[T], args: List[(Ty, T[Any])]): AtCall[T] = AtCall(args.map(_._1), g =>
    args.flatMap((ty, v) => g.of[T, Any](ty, s).map(_(v))).reduceOption(s.and).getOrElse(s.bool(true)))

  /** Each call below a condition. */
  def when[T[_]](s: Sym[T], c: T[Boolean])(calls: List[AtCall[T]]): List[AtCall[T]] =
    calls.map(a => AtCall(a.tys, g => s.implies(c, a.stated(g))))

  /** Each call below a binder, for every value of it meeting `ctx` when given, and nothing else (no rule is assumed
    * of a value the code binds: only `ctx`, its place, says what it is). Its calls are read once on a variable no term
    * binds, for their number and types, then each one under the binder.
    */
  def under[T[_], A](s: Sym[T], x: Bound[A], ctx: Option[T[A] => T[Boolean]])(body: T[A] => List[AtCall[T]])
      : List[AtCall[T]] =
    val probe = body(s.free[A](Binder(VarId.step(Int.MaxValue), x.hint, x.ty)))
    probe.indices.toList.map(j => AtCall(probe(j).tys, g => s.forall(x)(v =>
      ctx.fold(body(v)(j).stated(g))(c => s.implies(c(v), body(v)(j).stated(g))))))
