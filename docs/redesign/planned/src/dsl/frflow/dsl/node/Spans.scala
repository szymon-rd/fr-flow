package frflow.dsl.node

import frflow.core.name.RelPath

/** The project-relative path of a source file the compiler names (by the build's `frflow.sources` root). */
object Spans:
  def relative(file: String): RelPath = ???
