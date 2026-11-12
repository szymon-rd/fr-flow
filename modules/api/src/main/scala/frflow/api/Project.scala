package frflow.api

import frflow.api.view.NotMade
import frflow.core.Elaborated
import frflow.core.example.Example
import frflow.core.name.RelPath
import java.nio.file.Path

/** A project as a front end opens it: its model, its examples, the directories its sources are under (relative to the
  * project), and FrFlow's Lean library as the project's `lakefile.toml` requires it (relative to its `lean/`, so it may
  * lead out of the project); `unread`, each class of examples found among its test classes that could not be made, with
  * why.
  */
final case class Project(model: Elaborated, examples: List[Example], sources: List[RelPath], library: Path,
    unread: List[(String, NotMade)] = Nil)
