package frflow.core

/** A path a source names: `frflow.core.spec`, of the module `core`; the facade, `frflow`, of `eval`. */
final case class Ref(path: String):
  private val segments = path.split('.').toList.drop(1)
  val module: String = segments.headOption.getOrElse("eval")
  /** Whether it is in an edge's target: a module, or a package and its subpackages (`core.spec`). */
  def within(target: String): Boolean =
    val t = target.split('.').toList
    if segments.isEmpty then t == List("eval") else segments.take(t.size) == t
