package frflow.project.program

import frflow.core.name.RelPath
import frflow.project.port.RocqLibrary
import frflow.testing.Settings

/** A project as the shell reads it: the directories holding its sources (the files its nodes are written in and
  * govern), how its tests run, and FrFlow's Rocq library its proofs load.
  */
final case class Project(sources: List[RelPath], settings: Settings, library: RocqLibrary)
