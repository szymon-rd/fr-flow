package frflow.decision.ledger

import frflow.core.name.NodeId
import frflow.decision.content.{Framed, Sha}

/** Who may decide (`.frflow/deciders`): committed, each version naming the one before it (`after`, the hash of its
  * signed bytes) and signed by a key that version listed (the first by its own first entry). A decision counts only
  * when its key is listed under its decider's name. FrFlow reads the committed versions only, so filing a new key
  * under a new name, editing the file, or committing an older version again makes no one a decider. A version with
  * no seal follows none.
  */
final case class Deciders(entries: List[Decider], after: Option[String], seal: Option[Seal]):
  def allows(name: String, key: String): Boolean = entries.exists(d => d.name == name && d.key == key)

  /** Signed by a decider listed under its name, and the signature verifies. */
  def counts(verify: Seals.Verifier)(id: NodeId, d: Decision): Boolean =
    d.seal.exists(s => allows(d.author.by, s.key) && verify(s, Payload.of(id, d)))

  /** What its seal covers: the version it follows, then each entry's name, key and public key, framed. */
  def payload: Array[Byte] =
    Framed(after.getOrElse("") :: entries.size.toString :: entries.flatMap(d => List(d.name, d.key, d.publicKey)))

  /** What the next version names as the one it follows. */
  def ref: String = Sha.bytes(payload)

object Deciders:
  /** Whether `next` may follow `previous` (none for the first list): it names `previous`, and a key `previous` lists
    * signed it.
    */
  def follows(previous: Option[Deciders], next: Deciders, verify: Seals.Verifier): Boolean =
    val signers = previous.fold(next.entries.take(1))(_.entries)
    next.after == previous.map(_.ref) &&
      next.seal.exists(s => signers.exists(_.key == s.key) && verify(s, next.payload))

  /** The list that counts: the last committed version, when each version, oldest first, follows the one before. */
  def committed(versions: List[Deciders], verify: Seals.Verifier): Option[Deciders] =
    val linked = versions.zip(None :: versions.map(Some(_))).forall((next, prev) => follows(prev, next, verify))
    Option.when(linked)(versions.lastOption).flatten
