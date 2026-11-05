package frflow.dsl.node

import frflow.core.name.RelPath
import frflow.dsl.build.Source

/** A source file's path as the macros recorded it (`Source.relative`: relative to the build's directory, read when
  * the model was compiled), made a `RelPath`; the shell makes it relative to the project (`Relocate`).
  */
object Spans:
  def relative(file: String): RelPath = Source.path(file)
