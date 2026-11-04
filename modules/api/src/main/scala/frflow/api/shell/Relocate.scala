package frflow.api.shell

import frflow.core.Elaborated
import frflow.core.name.RelPath
import java.nio.file.Path

/** The files a model records (where each node is written, where code is given its Definitions, where the model is
  * assembled) made relative to the project's directory: the DSL records them as the compiler named them, relative to
  * where the build ran (`from`, the `frflow.sources` root or the working directory), and a project under
  * `examples/NAME` reads its sources relative to itself. A file outside the project is left as recorded.
  */
private[api] object Relocate:
  def apply(e: Elaborated, from: Path, to: Path): Elaborated =
    val t = e.theory
    def move(p: RelPath): RelPath =
      RelPath.parse(to.toAbsolutePath.normalize.relativize(from.toAbsolutePath.resolve(p.value).normalize).toString)
        .getOrElse(p)
    e.copy(theory = t.copy(nodes = t.nodes.map(s => s.copy(at = s.at.copy(file = move(s.at.file)))),
      code = t.code.copy(attached = t.code.attached.map((k, a) => k -> a.copy(writtenIn = move(a.writtenIn)))),
      writtenIn = t.writtenIn.map(move)))
