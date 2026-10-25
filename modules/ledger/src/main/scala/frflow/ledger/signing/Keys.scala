package frflow
package ledger
package signing

import cats.syntax.all.*
import frflow.protocol.*
import java.security.spec.{PKCS8EncodedKeySpec, X509EncodedKeySpec}
import java.security.{KeyFactory, KeyPairGenerator, PublicKey}
import java.util.Base64

/** Keys as text: a key file holds the private key (PKCS#8) and the public key (X.509) on two lines, in base64; a
  * `.pub` file, the public key on one.
  */
object Keys:
  private def b64(bytes: Array[Byte]) = Base64.getEncoder.encodeToString(bytes)
  private def unb64(s: String) = Either.catchNonFatal(Base64.getDecoder.decode(s.trim)).leftMap(_.getMessage)
  private def factory = KeyFactory.getInstance("Ed25519")
  def id(pub: PublicKey): KeyId = KeyId(Sha.bytes(pub.getEncoded).take(16))

  def generate(): DeveloperKey =
    val kp = KeyPairGenerator.getInstance("Ed25519").generateKeyPair()
    DeveloperKey(kp.getPrivate, kp.getPublic)

  def encode(k: DeveloperKey): String = b64(k.signing.getEncoded) + "\n" + b64(k.public.getEncoded) + "\n"
  def encodePublic(pub: PublicKey): String = b64(pub.getEncoded) + "\n"

  def decode(text: String): Either[String, DeveloperKey] =
    text.linesIterator.map(_.trim).filter(_.nonEmpty).toList match
      case priv :: pub :: _ =>
        for
          p <- unb64(priv).flatMap(b => Either.catchNonFatal(factory.generatePrivate(PKCS8EncodedKeySpec(b))).leftMap(_.getMessage))
          q <- decodePublic(pub)
        yield DeveloperKey(p, q)
      case _ => Left("expected two lines: the private key, then the public key")

  def decodePublic(line: String): Either[String, PublicKey] =
    unb64(line).flatMap(b => Either.catchNonFatal(factory.generatePublic(X509EncodedKeySpec(b))).leftMap(_.getMessage))
