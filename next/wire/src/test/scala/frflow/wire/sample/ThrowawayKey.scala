package frflow.wire.sample

import frflow.decision.content.Sha
import frflow.decision.ledger.{Seal, Seals}
import java.security.{KeyPairGenerator, Signature}
import java.util.Base64
import scala.util.Try

/** An Ed25519 key made in memory for one test run: never a developer's key, never written anywhere. Its verifier is
  * total: a signature that is not one (not Base64, the wrong length) does not verify.
  */
final class ThrowawayKey:
  private val pair = KeyPairGenerator.getInstance("Ed25519").generateKeyPair()
  val id: String = Sha(Base64.getEncoder.encodeToString(pair.getPublic.getEncoded)).take(16)
  val publicKey: String = Base64.getEncoder.encodeToString(pair.getPublic.getEncoded)

  val sign: Seals.Signer = bytes =>
    val s = Signature.getInstance("Ed25519")
    s.initSign(pair.getPrivate)
    s.update(bytes)
    Seal(id, Base64.getEncoder.encodeToString(s.sign()))

  def verifies(seal: Seal, bytes: Array[Byte]): Boolean = seal.key == id && Try {
    val s = Signature.getInstance("Ed25519")
    s.initVerify(pair.getPublic)
    s.update(bytes)
    s.verify(Base64.getDecoder.decode(seal.signature))
  }.getOrElse(false)

object ThrowawayKey:
  def verifier(keys: ThrowawayKey*): Seals.Verifier = (seal, bytes) => keys.exists(_.verifies(seal, bytes))
