package frflow.core.code

import frflow.core.name.RelPath

/** A project file plain Scala refers to, with the names of the definitions in it the Scala refers to: in a file that
  * holds nodes, only those are the code a node governs (owner §38); any other file is governed whole.
  */
final case class CodeFile(path: RelPath, names: List[String])

object CodeFile:
  /** One per file, in order of the paths, each with every name given it. */
  def merged(files: List[CodeFile]): List[CodeFile] =
    files.groupMap(_.path)(_.names).toList.sortBy(_._1).map((p, ns) => CodeFile(p, ns.flatten.distinct))
