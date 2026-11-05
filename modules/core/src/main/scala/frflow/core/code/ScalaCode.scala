package frflow.core.code

import frflow.core.name.SourceText

/** Plain Scala giving a Definition its meaning: the handle, its expression as written (decided), and the project files
  * that expression refers to, with what it refers to in each (governed).
  */
final case class ScalaCode(impl: Impl, written: SourceText, files: List[CodeFile])
