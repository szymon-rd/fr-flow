package frflow

import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path}
import java.security.{KeyFactory, KeyPairGenerator, PrivateKey, PublicKey, Signature}
import java.security.spec.{PKCS8EncodedKeySpec, X509EncodedKeySpec}
import java.util.Base64
import scala.jdk.CollectionConverters.*

/** Decisions signed by the developer's key, so one an agent wrote into the ledger shows.
  *
  * The browser server holds the private key, outside the repository (where agents do not run);
  * the public keys are committed in `.frflow/keys/<id>.pub`, so adding one shows in git. Every
  * decision must be signed by one of them, or `status` warns; with no key, no decision counts.
  */
object Signing:

  private def b64(bytes: Array[Byte]) = Base64.getEncoder.encodeToString(bytes)

  /** What is signed: everything the decision says, and which node it is about. */
  def payload(id: String, d: Decision): Array[Byte] =
    val u = d.unsigned
    Seq(id, u.action, u.by, u.at, u.reason, u.rejected.mkString(","), u.held.mkString(","), u.chain, u.code, u.commit, u.tree,
      u.after, Ledger.ref(u.content)).mkString("\u0000").getBytes(UTF_8)

  def keyId(pub: PublicKey): String =
    java.security.MessageDigest.getInstance("SHA-256").digest(pub.getEncoded).take(8).map("%02x".format(_)).mkString

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

  /** A key in `.frflow/keys/<id>.pub`: the public key, and, for any but the project's first key, a
    * certificate (the id of a developer key and its signature of this key).
    */
  final case class KeyFile(id: String, pub: PublicKey, certifiedBy: Option[(String, String)])

  private def parse(text: String): Option[KeyFile] =
    try
      val lines = text.linesIterator.map(_.trim).filter(_.nonEmpty).toList
      val pub = KeyFactory.getInstance("Ed25519").generatePublic(X509EncodedKeySpec(Base64.getDecoder.decode(lines.head)))
      val cert = lines.lift(1).map(_.split("\\s+").toList).collect { case List(by, sig) => (by, sig) }
      Some(KeyFile(keyId(pub), pub, cert))
    catch case _: Exception => None

  def keyFiles(dir: Path): List[KeyFile] =
    if !Files.isDirectory(dir) then Nil
    else Files.list(dir).iterator.asScala.toList.filter(_.toString.endsWith(".pub")).sortBy(_.toString)
      .flatMap(f => parse(Files.readString(f, UTF_8)))

  /** The developer keys: the project's one key without a certificate, and every key a developer key
    * certified. A second key without a certificate (a process that made its own) is not one.
    */
  def keys(dir: Path): Map[String, PublicKey] =
    val all = keyFiles(dir)
    def grow(trusted: Map[String, PublicKey]): Map[String, PublicKey] =
      val more = all.filter(k => !trusted.contains(k.id) && k.certifiedBy.exists((by, sig) => trusted.get(by).exists(t => verifyBytes(t, k.pub.getEncoded, sig))))
      if more.isEmpty then trusted else grow(trusted ++ more.map(k => k.id -> k.pub))
    // CI can name the developer's keys itself, out of any agent's reach.
    sys.env.get("FRFLOW_DEVELOPER_KEYS").map(_.split("[,\\s]+").filter(_.nonEmpty).toSet) match
      case Some(pinned) => grow(all.filter(k => pinned(k.id)).map(k => k.id -> k.pub).toMap)
      case None         => first(dir, all).fold(Map.empty)(k => grow(Map(k.id -> k.pub)))

  /** The project's first key: the one committed first, or, before any is committed, the only one. */
  private def first(dir: Path, all: List[KeyFile]): Option[KeyFile] =
    val committed = Git.firstAdded(dir).flatMap(f => all.find(k => f.endsWith(s"${k.id}.pub")))
    committed.orElse(all.filter(_.certifiedBy.isEmpty) match { case List(only) if Git.firstAdded(dir).isEmpty => Some(only); case _ => None })

  /** Who the developer key is, for `status` to show: pinned by CI, or the first committed (and by whom:
    * an agent that commits a key before the developer does would be it, so CI should pin it).
    */
  def firstKey(root: Path, dir: Path): Option[String] =
    sys.env.get("FRFLOW_DEVELOPER_KEYS").map(k => s"pinned by FRFLOW_DEVELOPER_KEYS ($k)").orElse {
      first(dir, keyFiles(dir)).map { k =>
        Git.addedBy(dir, s"${k.id}.pub").fold(s"${k.id} (not committed yet)")(by => s"${k.id}, first committed by $by; pin it in CI with FRFLOW_DEVELOPER_KEYS=${k.id}")
      }
    }

  /** Keys in `dir` that are not developer keys: each is a warning. */
  def untrusted(dir: Path): List[String] =
    val all = keyFiles(dir)
    val ok = keys(dir)
    all.filterNot(k => ok.contains(k.id)).map(k =>
      if k.certifiedBy.isEmpty then s"${k.id} is not a developer key: certify it from a browser that holds one, if it is yours, or remove it"
      else s"${k.id}: its certificate is not by a developer key")

  private def verifyBytes(pub: PublicKey, bytes: Array[Byte], sig: String): Boolean =
    try
      val s = Signature.getInstance("Ed25519")
      s.initVerify(pub)
      s.update(bytes)
      s.verify(Base64.getDecoder.decode(sig))
    catch case _: Exception => false

  /** Certifies `other` with the developer's key: it becomes a developer key of the project. */
  def certify(dir: Path, otherId: String, priv: PrivateKey, pub: PublicKey): Either[String, Unit] =
    keyFiles(dir).find(_.id == otherId) match
      case None => Left(s"no key $otherId in ${dir}")
      case Some(k) =>
        if !keys(dir).contains(keyId(pub)) then Left("this browser's key is not a developer key of the project")
        else
          val s = Signature.getInstance("Ed25519")
          s.initSign(priv)
          s.update(k.pub.getEncoded)
          Files.writeString(dir.resolve(s"$otherId.pub"), b64(k.pub.getEncoded) + "\n" + keyId(pub) + " " + b64(s.sign()) + "\n", UTF_8)
          Right(())

  /** The developer's decisions not signed by a developer key; none while the project has never had a key. */
  def unsigned(l: Ledger, dir: Path): List[(String, Decision)] =
    // Every decision is signed, from the first: with no developer key yet, none counts (anyone who can
    // write the ledger could have written it).
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

  /** Writes the public key into a project's `.frflow/keys`, if it is not there. */
  def publish(pub: PublicKey, dir: Path): Unit =
    val f = dir.resolve(s"${keyId(pub)}.pub")
    if !Files.exists(f) then
      Files.createDirectories(dir)
      Files.writeString(f, b64(pub.getEncoded) + "\n", UTF_8)

  /** Signs the decisions of the developer's in `now` that `before` did not have. */
  def signNew(before: Ledger, now: Ledger, priv: PrivateKey, pub: PublicKey): Ledger =
    Ledger(now.decisions.map { (id, ds) =>
      val old = before.history(id).map(_.unsigned).toSet
      id -> ds.map(d => if !old(d.unsigned) then sign(priv, pub, id, d) else d)
    })

  /** Signs the named decisions (by `Ledger.entry`), the developer vouching for them. */
  def signEntries(l: Ledger, entries: Set[String], priv: PrivateKey, pub: PublicKey): Ledger =
    Ledger(l.decisions.map((id, ds) => id -> ds.map(d => if entries(Ledger.entry(d)) then sign(priv, pub, id, d) else d)))
