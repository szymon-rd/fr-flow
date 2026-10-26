package frflow.dsl.node

import frflow.core.name.{NodeId, Span}
import frflow.core.spec.Prose

/** A head from what a constructor was given, the file the compiler names made relative to the project. */
object Heads:
  def make(id: String, prose: Prose, file: String, offset: Int): Head =
    Head(NodeId(id), prose, Span(Spans.relative(file), offset), Links.none)
