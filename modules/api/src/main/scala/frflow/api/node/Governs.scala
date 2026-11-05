package frflow.api.node

import frflow.core.name.RelPath

/** A path a design governs, and the project's files under it: none when it names no file of the project (`status`
  * warns of it too, `Warning.GovernedMissing`).
  */
final case class Governs(path: RelPath, files: List[RelPath]):
  def missing: Boolean = files.isEmpty
