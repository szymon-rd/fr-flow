package frflow.api.view.source

import frflow.core.name.RelPath

/** A project file a node's code is in: what of it the node governs, and its text (none when the project has no such
  * file).
  */
final case class SourceFile(path: RelPath, part: FilePart, text: Option[String])
