package frflow.dsl.node

import frflow.core.name.RelPath
import java.nio.file.Path

/** The project-relative path of a source file the compiler names, under the build's `frflow.sources` root (the
  * working directory by default); a file outside it is named by itself, from the build that compiled it.
  */
object Spans:
  def relative(file: String): RelPath =
    val root = Path.of(sys.props.getOrElse("frflow.sources", "")).toAbsolutePath
    val path = Path.of(file).toAbsolutePath
    RelPath.parse(root.relativize(path).toString).orElse(RelPath.parse(path.getFileName.toString))
      .fold(why => throw IllegalStateException(s"FrFlow bug: no relative path for $file: $why"), identity)
