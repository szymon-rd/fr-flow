package frflow.decision.content

import cats.Eq

/** A node as the developer decides it: named fields in a fixed order. `hash` ignores runs of whitespace; `ref` is the
  * exact recorded form, which a signature covers.
  */
final case class Content(fields: List[(String, FieldValue)]):
  def get(name: String): Option[FieldValue] = fields.collectFirst { case (`name`, v) => v }
  def text(name: String): String = get(name).collect { case FieldValue.Text(t) => t }.getOrElse("")
  def texts(name: String): List[String] = get(name).collect { case FieldValue.Texts(ts) => ts }.getOrElse(Nil)
  def only(keep: String => Boolean): Content = Content(fields.filter((k, _) => keep(k)))
  def without(drop: String => Boolean): Content = only(k => !drop(k))
  def hash: Hash = Hash(Sha(Canonical.print(Canonical.normal(this))))
  def ref: String = Sha(Canonical.print(this)).take(16)

object Content:
  val empty: Content = Content(Nil)
  given Eq[Content] = Eq.fromUniversalEquals
