package frflow.project.port.memory

import cats.Monad
import cats.effect.{Ref, Sync}
import cats.syntax.all.*
import frflow.decision.ledger.{Decider, Deciders, Seals}
import frflow.project.port.{KeyRing, Keys}
import java.security.{KeyPair, KeyPairGenerator}
import java.util.Base64

/** An Ed25519 key made in memory for one run, never written anywhere, and the deciders' list's versions as if
  * committed (`list` adds one): the decision tests never touch the developer's key.
  */
final class MemoryKeys[F[_]: Monad] private (pair: KeyPair, listed: Ref[F, List[Deciders]]) extends KeyRing[F]:
  val publicKey: String = Base64.getEncoder.encodeToString(pair.getPublic.getEncoded)
  val id: String = Keys.id(publicKey)
  private val sign: Seals.Signer = Keys.signer(pair.getPrivate, id)

  def signer: F[Seals.Signer] = sign.pure[F]
  def key: F[String] = id.pure[F]
  def verifier: F[Seals.Verifier] = listed.get.map(vs => Keys.verifier(vs.flatMap(_.entries)))
  def deciders: F[Option[Deciders]] = listed.get.map(KeyRing.committed)
  def lists: F[List[Deciders]] = listed.get

  /** This key under `name`. */
  def entry(name: String): Decider = Decider(name, id, publicKey)
  /** `d` sealed by this key. */
  def signed(d: Deciders): Deciders = d.copy(seal = Some(sign(d.payload)))
  /** A version committed after the others. */
  def list(d: Deciders): F[Unit] = listed.update(_ :+ d)

object MemoryKeys:
  /** A fresh key, and no deciders' list yet. */
  def apply[F[_]: Sync]: F[MemoryKeys[F]] =
    (Sync[F].delay(KeyPairGenerator.getInstance("Ed25519").generateKeyPair()), Ref.of[F, List[Deciders]](Nil))
      .mapN(new MemoryKeys(_, _))
