package frflow.dsl.node

import frflow.core.name.RelPath

/** A source file's path as the macros recorded it (`Source.relative`: relative to the build's directory, read when
  * the model was compiled), made a `RelPath`; the shell makes it relative to the project (`Relocate`).
  */
object Spans:
  def relative(file: String): RelPath =
    RelPath.parse(file).fold(why => throw IllegalStateException(s"FrFlow bug: no relative path for $file: $why"),
      identity)
