package frflow.decision

import frflow.decision.content.Sha
import frflow.decision.ledger.{Seal, Seals}
import java.security.{KeyPairGenerator, Signature}
import java.util.Base64

/** An Ed25519 key made in memory for one test run: never a developer's key, never written anywhere. */
final class TestKey:
  private val pair = KeyPairGenerator.getInstance("Ed25519").generateKeyPair()
  val id: String = Sha(Base64.getEncoder.encodeToString(pair.getPublic.getEncoded)).take(16)

  val sign: Seals.Signer = bytes =>
    val s = Signature.getInstance("Ed25519")
    s.initSign(pair.getPrivate)
    s.update(bytes)
    Seal(id, Base64.getEncoder.encodeToString(s.sign()))

  def verifies(seal: Seal, bytes: Array[Byte]): Boolean =
    val s = Signature.getInstance("Ed25519")
    s.initVerify(pair.getPublic)
    s.update(bytes)
    seal.key == id && s.verify(Base64.getDecoder.decode(seal.signature))

object TestKey:
  /** Verifies a seal by whichever of `keys` it names. */
  def verifier(keys: TestKey*): Seals.Verifier = (seal, bytes) =>
    keys.exists(k => k.id == seal.key && k.verifies(seal, bytes))
