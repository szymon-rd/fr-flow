package frflow
package ledger

import cats.effect.{IO, Resource}
import cats.syntax.all.*
import frflow.protocol.*
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path, Paths}
import java.nio.file.attribute.PosixFilePermissions
import java.security.{KeyFactory, KeyPairGenerator, PrivateKey, PublicKey, Signature}
import java.security.spec.{PKCS8EncodedKeySpec, X509EncodedKeySpec}
import java.util.Base64
import scala.jdk.CollectionConverters.*

/** The developer's key: the private key signs their decisions; the public one, filed in `.frflow/keys/NAME.pub`, verifies them. */
final case class DeveloperKey(signing: PrivateKey, public: PublicKey):
  def id: KeyId = Keys.id(public)

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

/** Decisions signed by the developer's key, so one written into the ledger by anyone else shows. Pure: the keys are given. */
object Signing:
  /** What is signed: everything the decision says, and which node it is about. */
  def payload(id: NodeId, d: Decision): Array[Byte] =
    val u = d.unsigned
    Seq(id.value, u.action.toString, u.by, u.at.toString, u.reason, u.rejected.mkString(","), u.chain.value, u.code.fold("")(_.value),
      u.commit.getOrElse(""), u.after.fold("")(_.value), u.content.ref)
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

  def unsigned(l: Ledger, keys: Map[KeyId, PublicKey]): List[(NodeId, Decision)] =
    l.decisions.toList.sortBy(_._1).flatMap((id, ds) => ds.filterNot(d => verify(keys, id, d)).map(id -> _))

  /** Signs the decisions in `now` that `before` did not have: the developer's new ones. */
  def signNew(before: Ledger, now: Ledger, key: DeveloperKey): Ledger =
    Ledger(now.decisions.map { (id, ds) =>
      val old = before.history(id).map(_.unsigned).toSet
      id -> ds.map(d => if !old(d.unsigned) then sign(key, id, d) else d)
    })

  /** What `status` warns about the record itself: no developer key, or the decisions `unsigned` lists. */
  def warnings(keys: Map[KeyId, PublicKey], now: Ledger, unsigned: List[(NodeId, Decision)]): List[String] =
    Option.when(now.decisions.nonEmpty && keys.isEmpty)(
      "no developer key: the developer signs their decisions with their key, and commits its public key in .frflow/keys/").toList ++
    unsigned.map((id, d) => s"$id: the ${d.action} of ${d.at} by ${d.by} is not signed by a developer key: the developer decides it again")

/** The keys on disk: the developer's signing key, outside the repository (which others may edit), and the project's
  * public keys in `.frflow/keys/NAME.pub`, committed.
  */
final class KeyStore private (keyFile: Path, keysDir: Path):
  /** The developer's key, created on first use, readable by its owner only (where the file system has permissions). */
  def developer: IO[DeveloperKey] = IO.blocking(Files.isRegularFile(keyFile)).ifM(read, create)

  private def read = IO.blocking(Files.readString(keyFile)).flatMap(text =>
    IO.fromEither(Keys.decode(text).leftMap(LedgerError.BadKey(keyFile, _))))

  private def create = IO(Keys.generate()).flatTap(k => IO.blocking {
    Files.createDirectories(keyFile.toAbsolutePath.getParent)
    val posix = keyFile.getFileSystem.supportedFileAttributeViews.contains("posix")
    val ownerOnly = if posix then List(PosixFilePermissions.asFileAttribute(PosixFilePermissions.fromString("rw-------"))) else Nil
    Files.createFile(keyFile, ownerOnly*)
    Files.writeString(keyFile, Keys.encode(k))
  })

  /** The name the developer's key is filed under (`NAME.pub`), if the key exists and is filed. */
  def filedName: IO[Option[String]] =
    IO.blocking(Files.isRegularFile(keyFile)).ifM(
      (read, KeyStore.filed(keysDir)).mapN((k, all) => all.collectFirst { case (name, pub) if Keys.id(pub) == k.id => name }),
      IO.pure(None))

  /** Files the public key as `NAME.pub` (`ID.pub` with no name), unless it is there under any name. */
  def publish(key: PublicKey, name: String): IO[Unit] =
    KeyStore.projectKeys(keysDir).flatMap { known =>
      val file = keysDir.resolve(s"${if name.trim.isEmpty then Keys.id(key).value else name.trim}.pub")
      Store.write(file, Keys.encodePublic(key)).unlessA(known.contains(Keys.id(key)))
    }

object KeyStore:
  /** `FRFLOW_KEY`, or `~/.config/frflow/signing.key`. */
  def keyFile(env: Map[String, String], home: Path): Path =
    env.get("FRFLOW_KEY").map(_.trim).filter(_.nonEmpty).fold(home.resolve(".config/frflow/signing.key"))(Paths.get(_))

  def at(keyFile: Path, keysDir: Path): KeyStore = new KeyStore(keyFile, keysDir)

  def projectKeys(keysDir: Path): IO[Map[KeyId, PublicKey]] = filed(keysDir).map(_.map((_, pub) => Keys.id(pub) -> pub).toMap)

  /** Every `.pub` in `keysDir` that reads: its name (the file's, without `.pub`), and the key. */
  private def filed(keysDir: Path): IO[List[(String, PublicKey)]] =
    val pubs = Resource.fromAutoCloseable(IO.blocking(Files.list(keysDir)))
      .use(files => IO.blocking(files.iterator.asScala.toList.filter(_.toString.endsWith(".pub")).sortBy(_.toString)))
    IO.blocking(Files.isDirectory(keysDir)).ifM(pubs, IO.pure(Nil)).flatMap(_.traverseFilter(f =>
      IO.blocking(Files.readString(f).linesIterator.map(_.trim).find(_.nonEmpty).flatMap(Keys.decodePublic(_).toOption)
        .map(f.getFileName.toString.stripSuffix(".pub") -> _))))
