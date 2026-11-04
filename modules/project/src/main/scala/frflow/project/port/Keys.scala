package frflow.project.port

import cats.syntax.all.*
import frflow.decision.content.Sha
import frflow.decision.ledger.{Decider, Seal, Seals}
import java.security.spec.{PKCS8EncodedKeySpec, X509EncodedKeySpec}
import java.security.{KeyFactory, PrivateKey, PublicKey, Signature}
import java.util.Base64

/** Ed25519 keys as FrFlow names and uses them: a key's id is the first 16 hex digits of the SHA-256 of its public
  * key in Base64; a signature is Base64. A developer's key file holds the private key (PKCS#8) and the public key
  * (X.509), each in Base64, on two lines.
  */
object Keys:
  def id(publicKey: String): String = Sha(publicKey).take(16)

  /** Signs with `key`, the seal naming `keyId`. */
  def signer(key: PrivateKey, keyId: String): Seals.Signer = bytes =>
    val s = Signature.getInstance("Ed25519")
    s.initSign(key)
    s.update(bytes)
    Seal(keyId, Base64.getEncoder.encodeToString(s.sign()))

  /** Total: a seal verifies only by an entry named by its key whose key is its public key's id, with a signature
    * that is Base64 of the right length and checks; anything else (not Base64, not a key) does not verify.
    */
  def verifier(entries: List[Decider]): Seals.Verifier =
    val keys = entries.filter(d => id(d.publicKey) == d.key).flatMap(d => public(d.publicKey).toOption.map(d.key -> _))
      .toMap
    (seal, bytes) => keys.get(seal.key).exists(k => Either.catchNonFatal {
      val s = Signature.getInstance("Ed25519")
      s.initVerify(k)
      s.update(bytes)
      s.verify(Base64.getDecoder.decode(seal.signature))
    }.getOrElse(false))

  /** A key file's private key, and its public key in Base64. */
  def read(text: String): Either[String, (PrivateKey, String)] =
    text.linesIterator.map(_.trim).filter(_.nonEmpty).toList match
      case priv :: pub :: _ =>
        for
          p <- Either.catchNonFatal(KeyFactory.getInstance("Ed25519")
                 .generatePrivate(PKCS8EncodedKeySpec(Base64.getDecoder.decode(priv)))).leftMap(_.toString)
          _ <- public(pub)
        yield (p, pub)
      case _                => Left("expected two lines: the private key, then the public key")

  private def public(base64: String): Either[String, PublicKey] = Either.catchNonFatal(
    KeyFactory.getInstance("Ed25519").generatePublic(X509EncodedKeySpec(Base64.getDecoder.decode(base64))))
    .leftMap(_.toString)
