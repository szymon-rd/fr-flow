package frflow.project.code

import frflow.core.name.RelPath

/** What of a file a node governs (owner §38): the file whole, or, in a file that holds nodes, the definitions the
  * code refers to (`Named`, read by `Definitions`), so that editing a node beside them brings nothing back.
  */
enum Governed:
  case Whole(path: RelPath)
  case Named(path: RelPath, names: List[String])

  def path: RelPath

  /** The text a fingerprint reads of the file's source. */
  def of(source: String): String = this match
    case Whole(_)        => ScalaTokens.significant(source)
    case Named(_, names) => Definitions.of(ScalaTokens.significant(source), names)
