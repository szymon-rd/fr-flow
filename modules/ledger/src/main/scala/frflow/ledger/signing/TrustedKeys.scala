package frflow
package ledger
package signing

import frflow.protocol.*
import java.security.PublicKey

/** The keys a decision counts by: each developer's public key as committed (`.frflow/keys/NAME.pub` at HEAD), and, for a
  * name not committed yet, the key as filed (how a developer starts). A key file that differs from its committed version
  * is not trusted: a rewritten file would make forged decisions verify. Outside git, the keys as filed.
  */
final case class TrustedKeys(byName: Map[String, PublicKey], changed: List[String] = Nil, uncommitted: List[String] = Nil):
  lazy val byId: Map[KeyId, PublicKey] = byName.values.map(k => Keys.id(k) -> k).toMap
  /** The name each key is filed under: a decision counts only by the key of the name it is made under. */
  lazy val names: Map[KeyId, String] = byName.map((n, k) => Keys.id(k) -> n)

  /** Why a decision as `name` signed with `key` is refused, before anything is written: another key is filed under the
    * name (as committed, or in the working tree), or the key is filed under another name.
    */
  def refusal(name: String, key: PublicKey, working: List[(String, PublicKey)]): Option[Refusal] =
    val id = Keys.id(key)
    val filed = byName.get(name).toList ++ working.collect { case (n, k) if n == name => k }
    filed.find(k => Keys.id(k) != id).map(_ => Refusal.OtherKey(name))
      .orElse(names.get(id).filter(_ != name).map(Refusal.KeyFiledAs(_, name)))

  /** What `status` warns of the key files themselves. */
  def warnings: List[String] =
    changed.map(n => s".frflow/keys/$n.pub differs from the committed key: FrFlow trusts the committed one (a key is replaced only in a commit of its own)") ++
      uncommitted.map(n => s".frflow/keys/$n.pub is not committed yet: decisions count by it, as a new developer's; commit it, or remove it if it is not one")

object TrustedKeys:
  /** `working`: the keys as filed now; `committed`: as at HEAD, or None outside git. */
  def of(working: List[(String, PublicKey)], committed: Option[List[(String, PublicKey)]]): TrustedKeys = committed match
    case None => TrustedKeys(working.toMap)
    case Some(c) =>
      val (now, was) = (working.toMap, c.toMap)
      TrustedKeys(now ++ was,
        changed = now.collect { case (n, k) if was.get(n).exists(t => Keys.id(t) != Keys.id(k)) => n }.toList.sorted,
        uncommitted = (now.keySet -- was.keySet).toList.sorted)
