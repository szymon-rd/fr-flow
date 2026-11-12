package frflow.dsl.compiled

import frflow.dsl.lifted.FrSpec
import scala.util.Try

/** A type's `FrSpec`, found where a compiled class is read: the one given in the type's companion (`derives
  * FrSpec`, `given FrSpec[T] = …`, an opaque type's companion's), taken from the companion object as the JVM
  * has it. The compiler reads a class after it is compiled, so no implicit search finds the spec; the rule is the
  * one the search follows for a type of the developer's.
  */
object Specs:
  /** The spec in the companion of the type named `scala` (`payments.Payment`, `shop.Stock.Item`), loaded by
    * `from`; none if it has no companion or the companion gives none. A type written at the top level of a file
    * beside other definitions (an opaque type) has its companion in the file's own object (`Ids$package`).
    */
  def given_(from: ClassLoader, scala: String): Option[FrSpec[Any]] =
    val path = scala.split('.').toList.map(_.stripSuffix("$"))
    companion(from, path).orElse(companion(from, path.filterNot(_.contains("$package")))).flatMap(module =>
      module.getClass.getMethods.toList.filter(m => m.getParameterCount == 0 &&
        classOf[FrSpec[?]].isAssignableFrom(m.getReturnType)).sortBy(_.getName).headOption
        .map(_.invoke(module).asInstanceOf[FrSpec[Any]]))

  /** The companion object of the type at `path`: a class nested in objects is named with `$` on the JVM, so each
    * split of the path into a package and nested names is tried, the longest package first.
    */
  private def companion(from: ClassLoader, path: List[String]): Option[Any] =
    (path.size to 1 by -1).iterator.map(k => path.take(k).mkString(".") + path.drop(k).map("$" + _).mkString + "$")
      .flatMap(name => Try(Class.forName(name, true, from)).toOption)
      .flatMap(c => Try(c.getField("MODULE$").get(null)).toOption).nextOption()
