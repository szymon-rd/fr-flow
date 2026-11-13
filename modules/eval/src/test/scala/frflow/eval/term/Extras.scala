package frflow.eval.term

import frflow.core.expr.Value
import frflow.core.Lang
import frflow.core.name.CtorName
import frflow.core.term.language.{Final, Sym}

/** Terms of the Rocq law written by hand, for what the generators reach rarely or not at all: a field read off a
  * constant record of an option.
  */
object Extras:
  private val big = Lang.big
  private def num[T[_]](s: Sym[T], n: Int): T[BigInt] = s.lit(BigInt(n), Value.Num(n), big)

  private def spare[T[_]](s: Sym[T], at: Option[Int]): T[Spare] =
    s.lit(Spare(at.map(BigInt(_))), Value.Data(CtorName("mk"), List(Value.Maybe(at.map(Value.Num(_))))), Spare.ty)

  val terms: List[Final[Boolean]] = List(
    [T[_]] => (s: Sym[T]) => s.eq(s.field(spare(s, Some(1)), Spare.at), s.some(num(s, 1))),
    [T[_]] => (s: Sym[T]) => s.isDefined(s.field(spare(s, None), Spare.at)),
    [T[_]] => (s: Sym[T]) => s.contains(s.cons(s.getOrElse(s.field(spare(s, Some(4)), Spare.at), num(s, 0)),
      s.nil[BigInt](big)), s.length(s.nil[BigInt](big))))
