package frflow.api.view.source

import frflow.core.name.RelPath

/** A Lean module: its name, its file under the project, and its text. */
final case class LeanText(module: String, file: RelPath, text: String)
