package frflow.eval.term

import frflow.core.Lang
import frflow.core.expr.Value
import frflow.core.name.{CtorName, ModelName}
import frflow.core.term.{Final, Sym, World}
import frflow.core.ty.Ty

/** Terms of the Lean law written by hand, for what the generators reach rarely or not at all: worlds unchanged with
  * faults aside (a world's faults are no model's state), and a field read off a constant record of an option.
  */
object Extras:
  private val big = Lang.big
  private val stored = ModelName("stored")
  private def num[T[_]](s: Sym[T], n: Int): T[BigInt] = s.lit(BigInt(n), Value.Num(n), big)

  /** A world holding `n` in `stored`, and `faults`: in Scala under `Faults.model`, as `Literals` holds them. */
  private def world[T[_]](s: Sym[T], n: Int, faults: List[Boolean]): T[World] =
    val held: Map[ModelName, Any] = Map(stored -> BigInt(n))
    s.lit(World.of(if faults.isEmpty then held else held.updated(frflow.eval.Faults.model, faults)),
      Value.World(List(stored -> Value.Num(n)), faults), Ty.World)

  private def spare[T[_]](s: Sym[T], at: Option[Int]): T[Spare] =
    s.lit(Spare(at.map(BigInt(_))), Value.Data(CtorName("mk"), List(Value.Maybe(at.map(Value.Num(_))))), Spare.ty)

  val terms: List[Final[Boolean]] = List(
    [T[_]] => (s: Sym[T]) => s.unchanged(world(s, 2, List(true)), world(s, 2, Nil)),
    [T[_]] => (s: Sym[T]) => s.unchanged(world(s, 2, Nil), world(s, 2, List(false, true))),
    [T[_]] => (s: Sym[T]) => s.unchanged(world(s, 3, List(true)), world(s, 2, List(true))),
    [T[_]] => (s: Sym[T]) => s.eq(s.field(spare(s, Some(1)), Spare.at), s.some(num(s, 1))),
    [T[_]] => (s: Sym[T]) => s.isDefined(s.field(spare(s, None), Spare.at)),
    [T[_]] => (s: Sym[T]) => s.contains(s.cons(s.getOrElse(s.field(spare(s, Some(4)), Spare.at), num(s, 0)),
      s.nil[BigInt](big)), s.length(s.nil[BigInt](big))))
