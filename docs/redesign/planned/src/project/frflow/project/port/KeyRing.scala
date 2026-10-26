package frflow.project.port

import frflow.decision.ledger.{Deciders, Seals}

/** The developer's signing key, and the committed deciders' list (`Deciders.committed` over the file's committed
  * versions, read through `Git`). An algebra so tests sign with a key made in memory.
  */
trait KeyRing[F[_]]:
  def signer: F[Seals.Signer]
  /** The id of the key `signer` signs with. */
  def key: F[String]
  def verifier: F[Seals.Verifier]
  def deciders: F[Option[Deciders]]
