package frflow
package ledger
package signing

import cats.syntax.all.*
import frflow.protocol.*
import java.nio.charset.StandardCharsets.UTF_8
import java.security.{PublicKey, Signature}
import java.util.Base64

/** Decisions signed by the developer's key, so one written into the ledger by anyone else shows. The keys are passed in. */
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
