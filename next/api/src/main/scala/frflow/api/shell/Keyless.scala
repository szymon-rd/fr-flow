package frflow.api.shell

import cats.MonadThrow
import frflow.decision.ledger.Seals
import frflow.decision.ledger.Deciders
import frflow.project.port.{FrFlowError, KeyRing}

/** No key at hand (`env` gives neither `FRFLOW_KEY` nor `HOME`): signing raises `NoKey`; who may decide is still
  * `listed`'s, read from git.
  */
private[api] final class Keyless[F[_]: MonadThrow](listed: KeyRing[F]) extends KeyRing[F]:
  def signer: F[Seals.Signer] = none
  def key: F[String] = none
  def verifier: F[Seals.Verifier] = listed.verifier
  def deciders: F[Option[Deciders]] = listed.deciders
  private def none[A]: F[A] = MonadThrow[F].raiseError(FrFlowError.NoKey("FRFLOW_KEY"))
