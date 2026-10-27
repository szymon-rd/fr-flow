package frflow.api

import frflow.core.Elaborated
import frflow.core.example.Example
import frflow.core.name.RelPath

/** A project as a front end opens it: its model, its examples, its stores' implementations to test against their
  * models, the directories its sources are under (relative to the project), and FrFlow's Lean library as the
  * project's `lakefile.toml` requires it (relative to its `lean/`).
  */
final case class Project[F[_]](model: Elaborated, examples: List[Example], adapters: List[Adapter[F]],
    sources: List[RelPath], library: String)
