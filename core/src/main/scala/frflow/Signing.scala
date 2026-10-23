package frflow

import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path}
import java.security.{KeyFactory, KeyPairGenerator, PrivateKey, PublicKey, Signature}
import java.security.spec.{PKCS8EncodedKeySpec, X509EncodedKeySpec}
import java.util.Base64
import scala.jdk.CollectionConverters.*

/** Decisions signed by the developer's key, so one an agent wrote into the ledger shows.
  *
  * The developer holds the private key, outside the repository; the public keys are
  * committed in `.frflow/keys/<id>.pub`. Every decision must be signed by one of them, or `status` warns.
  */
object Signing:

  private def b64(bytes: Array[Byte]) = Base64.getEncoder.encodeToString(bytes)

  /** What is signed: everything the decision says, and which node it is about. */
  def payload(id: String, d: Decision): Array[Byte] =
    val u = d.unsigned
    Seq(id, u.action, u.by, u.at, u.reason, u.rejected.mkString(","), u.chain, u.code, u.commit, u.tree,
      u.after, Ledger.ref(u.content))
      .mkString("\u0000").getBytes(UTF_8)

  def keyId(pub: PublicKey): String =
    Sha.bytes(pub.getEncoded).take(16)

  def sign(priv: PrivateKey, pub: PublicKey, id: String, d: Decision): Decision =
    val s = Signature.getInstance("Ed25519")
    s.initSign(priv)
    s.update(payload(id, d))
    d.copy(key = keyId(pub), sig = b64(s.sign()))

  def verify(keys: Map[String, PublicKey], id: String, d: Decision): Boolean =
    keys.get(d.key).exists { pub =>
      try
        val s = Signature.getInstance("Ed25519")
        s.initVerify(pub)
        s.update(payload(id, d))
        s.verify(Base64.getDecoder.decode(d.sig))
      catch case _: Exception => false
    }

  /** The developer keys: every public key in `dir` (`<name>.pub`), by its id. */
  def keys(dir: Path): Map[String, PublicKey] =
    if !Files.isDirectory(dir) then Map.empty
    else Files.list(dir).iterator.asScala.toList.filter(_.toString.endsWith(".pub")).sortBy(_.toString).flatMap { f =>
      try
        val line = Files.readString(f, UTF_8).linesIterator.map(_.trim).find(_.nonEmpty).get
        val pub = KeyFactory.getInstance("Ed25519").generatePublic(X509EncodedKeySpec(Base64.getDecoder.decode(line)))
        Some(keyId(pub) -> pub)
      catch case _: Exception => None
    }.toMap

  /** The developer's decisions not signed by a developer key; none while the project has never had a key. */
  def unsigned(l: Ledger, dir: Path): List[(String, Decision)] =
    val keys = this.keys(dir)
    l.decisions.toList.sortBy(_._1).flatMap((id, ds) => ds.filterNot(d => verify(keys, id, d)).map(id -> _))

  /** The signing key at `file` (created if missing), with its public key. */
  def loadOrCreate(file: Path): (PrivateKey, PublicKey) =
    val kf = KeyFactory.getInstance("Ed25519")
    if Files.isRegularFile(file) then
      val lines = Files.readAllLines(file, UTF_8).asScala.toList
      (kf.generatePrivate(PKCS8EncodedKeySpec(Base64.getDecoder.decode(lines(0)))),
        kf.generatePublic(X509EncodedKeySpec(Base64.getDecoder.decode(lines(1)))))
    else
      val kp = KeyPairGenerator.getInstance("Ed25519").generateKeyPair()
      Files.createDirectories(file.getParent)
      Files.writeString(file, b64(kp.getPrivate.getEncoded) + "\n" + b64(kp.getPublic.getEncoded) + "\n", UTF_8)
      try Files.setPosixFilePermissions(file, java.nio.file.attribute.PosixFilePermissions.fromString("rw-------"))
      catch case _: Exception => ()
      (kp.getPrivate, kp.getPublic)

  /** Writes the public key into a project's `.frflow/keys` as `<name>.pub` (`<id>.pub` with no name),
    * if it is not there under any name.
    */
  def publish(pub: PublicKey, dir: Path, name: String = ""): Unit =
    if !keys(dir).contains(keyId(pub)) then
      Files.createDirectories(dir)
      Files.writeString(dir.resolve(s"${if name.trim.isEmpty then keyId(pub) else name.trim}.pub"), b64(pub.getEncoded) + "\n", UTF_8)

  /** Signs the decisions of the developer's in `now` that `before` did not have. */
  def signNew(before: Ledger, now: Ledger, priv: PrivateKey, pub: PublicKey): Ledger =
    Ledger(now.decisions.map { (id, ds) =>
      val old = before.history(id).map(_.unsigned).toSet
      id -> ds.map(d => if !old(d.unsigned) then sign(priv, pub, id, d) else d)
    })

  /** Signs the named decisions (by `Ledger.entry`), the developer vouching for them. */
  def signEntries(l: Ledger, entries: Set[String], priv: PrivateKey, pub: PublicKey): Ledger =
    Ledger(l.decisions.map((id, ds) => id -> ds.map(d => if entries(Ledger.entry(d)) then sign(priv, pub, id, d) else d)))

  /** What `status` warns about the record itself: decisions not signed by a key in
    * `.frflow/keys` (the developer's, who signs with it).
    */
  def warnings(file: Path, now: Ledger): List[String] =
    val dir = file.getParent.resolve("keys")
    (if now.decisions.nonEmpty && keys(dir).isEmpty then
      List("no developer key: the developer signs their decisions with their key, and commits its public key in .frflow/keys/") else Nil) ++
    unsigned(now, dir).map((id, d) =>
      s"$id: the ${d.action} of ${d.at} by ${d.by} is not signed by a developer key: the developer decides it again, or signs it if it is theirs")
