package frflow
package ledger

import cats.syntax.all.*
import frflow.protocol.*
import java.nio.charset.StandardCharsets.UTF_8
import java.security.{KeyFactory, KeyPairGenerator, PrivateKey, PublicKey, Signature}
import java.security.spec.{PKCS8EncodedKeySpec, X509EncodedKeySpec}
import java.util.Base64

/** The developer's key: the private key signs their decisions; the public one, filed in the project's
  * `.frflow/keys/NAME.pub`, verifies them.
  */
final case class DeveloperKey(signing: PrivateKey, public: PublicKey):
  def id: KeyId = Keys.id(public)

/** Keys as text: a key file holds the private key (PKCS#8) and the public key (X.509) on two lines, in
  * base64; a `.pub` file, the public key on one.
  */
object Keys:
  private def b64(bytes: Array[Byte]) = Base64.getEncoder.encodeToString(bytes)
  private def unb64(s: String) = Either.catchNonFatal(Base64.getDecoder.decode(s.trim)).leftMap(_.getMessage)
  private def factory = KeyFactory.getInstance("Ed25519")

  def id(pub: PublicKey): KeyId = KeyId(Sha.bytes(pub.getEncoded).take(16))

  /** A new key pair. */
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

/** Decisions signed by the developer's key, so one an agent wrote into the ledger shows. Pure: the keys
  * are given (see `KeyStore` for reading them).
  */
object Signing:

  /** What is signed: everything the decision says, and which node it is about. */
  def payload(id: NodeId, d: Decision): Array[Byte] =
    val u = d.unsigned
    Seq(id.value, u.action.toString, u.by, u.at, u.reason, u.rejected.mkString(","), u.chain.value, u.code.fold("")(_.value),
      u.commit.getOrElse(""), u.tree.getOrElse(""), u.after.fold("")(_.value), u.content.ref)
      .mkString("\u0000").getBytes(UTF_8)

  def sign(key: DeveloperKey, id: NodeId, d: Decision): Decision =
    val s = Signature.getInstance("Ed25519")
    s.initSign(key.signing)
    s.update(payload(id, d))
    d.copy(key = Some(key.id), sig = Some(Base64.getEncoder.encodeToString(s.sign())))

  /** Signed by one of `keys`, and unchanged since. */
  def verify(keys: Map[KeyId, PublicKey], id: NodeId, d: Decision): Boolean =
    d.key.flatMap(keys.get).zip(d.sig).exists { (pub, sig) =>
      Either.catchNonFatal {
        val s = Signature.getInstance("Ed25519")
        s.initVerify(pub)
        s.update(payload(id, d))
        s.verify(Base64.getDecoder.decode(sig))
      }.getOrElse(false)
    }

  /** The decisions not signed by one of `keys`. */
  def unsigned(l: Ledger, keys: Map[KeyId, PublicKey]): List[(NodeId, Decision)] =
    l.decisions.toList.sortBy(_._1).flatMap((id, ds) => ds.filterNot(d => verify(keys, id, d)).map(id -> _))

  /** Signs the decisions in `now` that `before` did not have: the developer's new ones. */
  def signNew(before: Ledger, now: Ledger, key: DeveloperKey): Ledger =
    Ledger(now.decisions.map { (id, ds) =>
      val old = before.history(id).map(_.unsigned).toSet
      id -> ds.map(d => if !old(d.unsigned) then sign(key, id, d) else d)
    })

  /** Signs the named decisions (by `Ledger.entry`), the developer vouching for them. */
  def signEntries(l: Ledger, entries: Set[EntryRef], key: DeveloperKey): Ledger =
    Ledger(l.decisions.map((id, ds) => id -> ds.map(d => if entries(Ledger.entry(d)) then sign(key, id, d) else d)))

  /** What `status` warns about the record itself: no developer key, or decisions not signed by one of
    * the project's keys (the developer's, who signs with it).
    */
  def warnings(keys: Map[KeyId, PublicKey], now: Ledger): List[String] =
    Option.when(now.decisions.nonEmpty && keys.isEmpty)(
      "no developer key: the developer signs their decisions with their key, and commits its public key in .frflow/keys/").toList ++
    unsigned(now, keys).map((id, d) =>
      s"$id: the ${d.action} of ${d.at} by ${d.by} is not signed by a developer key: the developer decides it again, or signs it if it is theirs")
