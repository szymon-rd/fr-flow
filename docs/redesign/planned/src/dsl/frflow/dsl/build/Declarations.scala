package frflow.dsl.build

import cats.kernel.Monoid
import frflow.core.expr.Lambda
import frflow.core.name.{BoundaryName, DefName, SymbolName, TypeName}
import frflow.core.spec.Written
import frflow.core.vocab.{BoundarySig, Sort, StateModel, Symbol}

/** The vocabulary something mentions, by name: a monoid merged by every term, so no registry is needed. Two different
  * declarations of one name are both kept, for `Validate` to report.
  */
final case class Declarations(types: Map[TypeName, List[Declared]], sorts: Map[TypeName, List[Sort]],
    symbols: Map[SymbolName, List[Symbol]], defines: Map[DefName, List[Deferred[Written[Lambda]]]],
    worlds: Map[BoundaryName, List[(BoundarySig, StateModel)]])

object Declarations:
  val none: Declarations = Declarations(Map.empty, Map.empty, Map.empty, Map.empty, Map.empty)
  given Monoid[Declarations] = Monoid.instance(none, (a, b) =>
    Declarations(union(a.types, b.types)(_.data), union(a.sorts, b.sorts)(identity),
      union(a.symbols, b.symbols)(identity), union(a.defines, b.defines)(identity),
      union(a.worlds, b.worlds)(identity)))

  def of(d: Declared): Declarations = none.copy(types = Map(d.data.typeName -> List(d)))
  def sort(s: Sort): Declarations = none.copy(sorts = Map(s.name -> List(s)))
  def symbol(s: Symbol): Declarations = none.copy(symbols = Map(s.name -> List(s)))
  def define(name: DefName, lambda: Deferred[Written[Lambda]]): Declarations =
    none.copy(defines = Map(name -> List(lambda)))
  /** A boundary with the model it is proven against (`Node.assumption`). */
  def boundary(b: BoundarySig, m: StateModel): Declarations = none.copy(worlds = Map(b.name -> List(b -> m)))

  /** Per name, the declarations of both, each once (`same` says which are one: a type by its declaration, a define
    * by its value, the one `Def` it comes from).
    */
  private def union[K, V](a: Map[K, List[V]], b: Map[K, List[V]])(same: V => Any): Map[K, List[V]] =
    (a.keySet ++ b.keySet).iterator.map(k => k -> (a.getOrElse(k, Nil) ++ b.getOrElse(k, Nil)).distinctBy(same)).toMap
