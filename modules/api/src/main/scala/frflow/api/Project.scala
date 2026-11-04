package frflow.api

import frflow.core.Elaborated
import frflow.core.example.Example
import frflow.core.name.RelPath
import java.nio.file.Path

/** A project as a front end opens it: its model (with the plain Scala of its models' operations, tested against
  * them, `implementTested(ops*)(…)`), its examples, the directories its sources are under (relative to the project),
  * and FrFlow's Lean library as the project's `lakefile.toml` requires it (relative to its `lean/`, so it may lead out
  * of the project).
  */
final case class Project(model: Elaborated, examples: List[Example], sources: List[RelPath], library: Path)
