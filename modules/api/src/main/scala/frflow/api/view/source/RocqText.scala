package frflow.api.view.source

import frflow.core.name.RelPath

/** A Rocq module: its name, its file under the project, and its text. */
final case class RocqText(module: String, file: RelPath, text: String)
