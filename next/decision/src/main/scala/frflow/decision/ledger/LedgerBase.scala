package frflow.decision.ledger

import frflow.decision.content.{Framed, Sha}

/** Where the ledger's committed history is read from (`.frflow/ledger-base`): the SHA-256 of a ledger file's text a
  * listed decider accepts as it is, the version of the base it follows (`after`, the hash of its signed bytes; absent
  * for the first), and its seal. The history a ledger is counted against (`Counted`) starts at the commit that made
  * the base that counts, whose ledger text must be the one the base names; every later committed version still
  * counts, so a text committed again later rewrites nothing unseen. An unreadable committed ledger, a committed
  * deletion or a merge of two branches' decisions the owner accepts then no longer locks deciding. A version with no
  * seal follows none.
  */
final case class LedgerBase(ledger: String, after: Option[String], seal: Option[Seal]):
  /** What its seal covers: the version it follows, then the ledger's hash, framed. */
  def payload: Array[Byte] = Framed(List(after.getOrElse(""), ledger))

  /** What the next version names as the one it follows. */
  def ref: String = Sha.bytes(payload)

object LedgerBase:
  /** A base accepting the ledger file's `text`, after `previous`, not yet sealed. */
  def of(text: String, previous: Option[LedgerBase]): LedgerBase = LedgerBase(Sha(text), previous.map(_.ref), None)

  /** Whether `next` may follow `previous` (none for the first): it names `previous`, and a key some committed version
    * of the deciders' list held (`ever`) signed it.
    */
  def follows(previous: Option[LedgerBase], next: LedgerBase, ever: List[Decider], verify: Seals.Verifier): Boolean =
    next.after == previous.map(_.ref) &&
      next.seal.exists(s => ever.exists(_.key == s.key) && verify(s, next.payload))

  /** The base that counts: the last committed version, when each, oldest first, follows the one before (signed by a
    * key some committed version of the deciders' list held), and the last is signed by a key the list that counts
    * now holds; none without a list.
    */
  def committed(versions: List[LedgerBase], lists: List[Deciders], now: Option[Deciders], verify: Seals.Verifier)
      : Option[LedgerBase] =
    val ever = lists.flatMap(_.entries)
    val linked = versions.zip(None :: versions.map(Some(_))).forall((next, prev) => follows(prev, next, ever, verify))
    versions.lastOption.filter(b => linked && now.exists(l => b.seal.exists(s => l.entries.exists(_.key == s.key))))

  /** The committed ledger texts a ledger is counted against, oldest first, each text once in a row, from `commits`
    * (each commit touching the ledger or its base, oldest first: the base that commit holds, read, and the ledger's
    * text): from the commit that made `base`, when its ledger text is the one `base` names (`true`); else all of them
    * (`false`: the base does not take).
    */
  def from(commits: List[(Option[LedgerBase], Option[String])], base: LedgerBase): (List[String], Boolean) =
    val made = commits.indexWhere(_._1.contains(base))
    val taken = commits.lift(made).flatMap(_._2).exists(t => Sha(t) == base.ledger)
    (texts(if taken then commits.drop(made) else commits), taken)

  /** The ledger's texts, each once in a row. */
  def texts(commits: List[(Option[LedgerBase], Option[String])]): List[String] =
    commits.flatMap(_._2).foldLeft(List.empty[String])((ts, t) => if ts.headOption.contains(t) then ts else t :: ts)
      .reverse
