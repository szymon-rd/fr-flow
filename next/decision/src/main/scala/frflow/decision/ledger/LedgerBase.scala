package frflow.decision.ledger

import frflow.decision.content.{Framed, Sha}

/** Where the ledger's committed history is read from (`.frflow/ledger-base`): the SHA-256 of a ledger file's text a
  * listed decider accepts as it is, the version of the base it follows (`after`, the hash of its signed bytes; absent
  * for the first), and its seal. Committed, each version signed by a key the committed deciders' list holds: the
  * history a ledger is counted against (`Counted`) starts at the last committed ledger whose text is the base's, so
  * an unreadable committed ledger, a committed deletion or a merge of two branches' decisions the owner accepts no
  * longer locks deciding. A version with no seal follows none.
  */
final case class LedgerBase(ledger: String, after: Option[String], seal: Option[Seal]):
  /** What its seal covers: the version it follows, then the ledger's hash, framed. */
  def payload: Array[Byte] = Framed(List(after.getOrElse(""), ledger))

  /** What the next version names as the one it follows. */
  def ref: String = Sha.bytes(payload)

object LedgerBase:
  /** A base accepting the ledger file's `text`, after `previous`, not yet sealed. */
  def of(text: String, previous: Option[LedgerBase]): LedgerBase = LedgerBase(Sha(text), previous.map(_.ref), None)

  /** Whether `next` may follow `previous` (none for the first): it names `previous`, and a key `deciders` lists
    * under some name signed it.
    */
  def follows(previous: Option[LedgerBase], next: LedgerBase, deciders: Deciders, verify: Seals.Verifier): Boolean =
    next.after == previous.map(_.ref) &&
      next.seal.exists(s => deciders.entries.exists(_.key == s.key) && verify(s, next.payload))

  /** The base that counts: the last committed version, when each, oldest first, follows the one before; none
    * without a deciders' list.
    */
  def committed(versions: List[LedgerBase], deciders: Option[Deciders], verify: Seals.Verifier): Option[LedgerBase] =
    deciders.flatMap { list =>
      val linked = versions.zip(None :: versions.map(Some(_))).forall((next, prev) => follows(prev, next, list, verify))
      Option.when(linked)(versions.lastOption).flatten
    }

  /** The committed ledger texts, oldest first, from the last one the base accepts; all of them without a base, or
    * when none is the base's.
    */
  def from(texts: List[String], base: Option[LedgerBase]): List[String] =
    base.map(b => texts.lastIndexWhere(t => Sha(t) == b.ledger)).filter(_ >= 0).fold(texts)(texts.drop)
