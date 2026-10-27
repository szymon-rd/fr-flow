package frflow.testing.derive

import frflow.core.example.Example
import frflow.core.expr.{Expr, Exprs, Value}
import frflow.core.ty.Ty
import frflow.core.vocab.{SymbolType, Vocabulary}

/** The examples' values by type, each value they hold too (a list's elements, a record's fields), and their numbers:
  * what derived values are drawn near, so a generated case often starts from what an example shows.
  */
final case class Seeds(byType: Map[Ty, Vector[Value]], numbers: Vector[BigInt]):
  def of(ty: Ty): Vector[Value] = byType.getOrElse(ty, Vector.empty)

object Seeds:
  val none: Seeds = Seeds(Map.empty, Vector.empty)

  /** Each constant an example's fact is written with, and each value it gives, with the values they hold. */
  def of(v: Vocabulary, examples: List[Example]): Seeds =
    val written = examples.flatMap(e => Exprs.all(e.fact.value).collect { case Expr.Lit(x, ty) => x -> ty } ++
      e.givens.flatMap(g => v.symbol(g.symbol).map(_.ty).collect { case SymbolType.Typed(ty) => g.value -> ty }))
    val parts = written.flatMap((x, ty) => Parts(v)(x, ty)).distinct
    Seeds(parts.groupMap(_._2)(_._1).view.mapValues(_.toVector).toMap,
      parts.collect { case (Value.Num(n), _) => n }.toVector.distinct)
