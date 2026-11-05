package frflow.project.program

import frflow.core.name.RelPath
import frflow.project.port.LeanLibrary
import frflow.testing.Settings

/** A project as the shell reads it: the directories holding its sources (the files its nodes are written in and
  * govern), how its tests run, and FrFlow's Lean library its Lean requires.
  */
final case class Project(sources: List[RelPath], settings: Settings, library: LeanLibrary)
