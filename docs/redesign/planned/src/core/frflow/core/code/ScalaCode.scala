package frflow.core.code

import frflow.core.name.{RelPath, SourceText}

/** Plain Scala giving a Definition its meaning: the handle, its expression as written (decided), and the project files
  * that expression refers to (governed).
  */
final case class ScalaCode(impl: Impl, written: SourceText, files: List[RelPath])
