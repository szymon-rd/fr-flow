package frflow.project.pipeline

import frflow.core.name.RelPath
import frflow.decision.ledger.Counted
import frflow.testing.Settings
import java.time.Instant

/** What a run reads, each once, through the algebras (`program.ReadInputs`): the ledger as it counts (with the
  * decisions that do not, and why), what earlier runs recorded, what Lean reads beside the generated modules (the
  * proof files and FrFlow's library), the project's sources, the time, and how the tests run (the cases, and the
  * seed the environment may give).
  */
final case class Inputs(ledger: Counted, recorded: Recorded, lean: LeanSources, sources: Map[RelPath, String],
    now: Instant, settings: Settings)
