package frflow.api.shell

import frflow.core.Elaborated
import frflow.core.code.{Code, CodeFile, Implementation}
import frflow.core.name.RelPath
import java.nio.file.Path

/** The files a model records (where each node is written, where code is given its Definitions, the files that code
  * refers to, where the model is assembled) made relative to the project's directory: the DSL records them as the
  * compiler named them, relative to the working directory the build ran in (`from`), and a project under
  * `examples/NAME` reads its sources relative to itself. A file outside the project is left as recorded.
  */
private[api] object Relocate:
  def apply(e: Elaborated, from: Path, to: Path): Elaborated =
    val t = e.theory
    def move(p: RelPath): RelPath =
      RelPath.parse(to.toAbsolutePath.normalize.relativize(from.toAbsolutePath.resolve(p.value).normalize).toString)
        .getOrElse(p)
    def files(fs: List[CodeFile]): List[CodeFile] = fs.map(f => f.copy(path = move(f.path)))
    def code(c: Code): Code = c match
      case Code.Tested(r, calls) => Code.Tested(r.copy(files = files(r.files)), calls)
      case other                 => other
    val implemented = t.code.implemented.map((m, i) => m -> Implementation(i.ops, i.scala, i.effect, i.written,
      files(i.files)))
    e.copy(theory = t.copy(nodes = t.nodes.map(s => s.copy(at = s.at.copy(file = move(s.at.file)))),
      code = t.code.copy(attached = t.code.attached.map((k, a) =>
        k -> a.copy(code = code(a.code), writtenIn = move(a.writtenIn))), implemented = implemented),
      writtenIn = t.writtenIn.map(move)))
