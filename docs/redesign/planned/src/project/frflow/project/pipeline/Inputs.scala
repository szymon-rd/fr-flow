package frflow.project.pipeline

import frflow.core.name.{NodeId, RelPath}
import frflow.decision.ledger.Ledger
import frflow.proof.reading.ProofFile
import java.time.Instant

/** What a run reads, each once, through the algebras (`program.ReadInputs`). */
final case class Inputs(
    ledger: Ledger,
    recorded: Recorded,
    proofs: Map[NodeId, ProofFile],
    sources: Map[RelPath, String],
    now: Instant)
