package frflow.dsl.build

import cats.kernel.Monoid
import cats.syntax.all.*
import frflow.core.expr.Lambda
import frflow.core.name.{DefName, RelPath, SymbolName, TypeName}
import frflow.core.spec.Written
import frflow.core.vocab.{Sort, Symbol}

/** The vocabulary something mentions, by name: a monoid merged by every term, so no registry is needed. Two different
  * declarations of one name are both kept, for `Validate` to report. `written`: the names of what is declared, by
  * the file it is written in, as the compiler named it (`Source.path`); `referred`: what plain Scala refers to, by
  * file (`SourceFiles`).
  */
final case class Declarations(types: Map[TypeName, List[Declared]], sorts: Map[TypeName, List[Sort]],
    symbols: Map[SymbolName, List[Symbol]], defines: Map[DefName, List[Deferred[Written[Lambda]]]],
    written: Map[RelPath, Set[String]], referred: Map[RelPath, Set[String]])

object Declarations:
  val none: Declarations = Declarations(Map.empty, Map.empty, Map.empty, Map.empty, Map.empty, Map.empty)
  given Monoid[Declarations] = Monoid.instance(none, (a, b) =>
    Declarations(union(a.types, b.types)(_.data), union(a.sorts, b.sorts)(identity),
      union(a.symbols, b.symbols)(identity), union(a.defines, b.defines)(identity), a.written |+| b.written,
      a.referred |+| b.referred))

  /** That `name` is declared in `file` (none: in FrFlow's own sources). */
  def in(file: Option[RelPath], name: String): Declarations = none.copy(written = file.map(_ -> Set(name)).toMap)
  /** That plain Scala refers to these definitions of these files. */
  def refers(files: List[(RelPath, List[String])]): Declarations =
    none.copy(referred = files.groupMapReduce(_._1)(_._2.toSet)(_ ++ _))
  def of(d: Declared): Declarations = none.copy(types = Map(d.data.typeName -> List(d)))
  def sort(s: Sort): Declarations = none.copy(sorts = Map(s.name -> List(s)))
  def symbol(s: Symbol): Declarations = none.copy(symbols = Map(s.name -> List(s)))
  def define(name: DefName, lambda: Deferred[Written[Lambda]]): Declarations =
    none.copy(defines = Map(name -> List(lambda)))
  /** Per name, the declarations of both, each once (`same` says which are one: a type by its declaration, a define
    * by its value, the one `Def` it comes from).
    */
  private def union[K, V](a: Map[K, List[V]], b: Map[K, List[V]])(same: V => Any): Map[K, List[V]] =
    (a.keySet ++ b.keySet).iterator.map(k => k -> (a.getOrElse(k, Nil) ++ b.getOrElse(k, Nil)).distinctBy(same)).toMap
