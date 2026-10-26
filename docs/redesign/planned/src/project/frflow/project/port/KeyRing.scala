package frflow.project.port

import frflow.decision.ledger.Seals

/** The developer's signing key and the project's public keys. An algebra so tests sign with a key made in memory. */
trait KeyRing[F[_]]:
  /** The developer's key, created on first use. */
  def signer: F[Seals.Signer]
  def verifier: F[Seals.Verifier]
  def publish(name: String): F[Unit]
  def filedName: F[Option[String]]
