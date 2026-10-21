package frflow.fixtures

/** A stock item.
  * @param name item name
  * @param qty  quantity in stock
  * @param tags labels
  */
final case class Item(name: String, qty: Int, tags: Set[String])

enum Color:
  case Red, Green
  case Custom(code: Int)

final case class Inventory(items: Map[String, Item], log: List[String]):
  /** Whether an item is stocked. */
  def has(name: String): Boolean = items.contains(name)

object Rules:
  val Limit: Int = 100
  def ok(i: Item): Boolean = i.qty <= Limit

package a:
  final case class Dup(x: Int)

package b:
  final case class Dup(y: Int)

/** Overrides equality: Scala `==` is not structural. */
final case class Odd(x: Int):
  override def equals(o: Any): Boolean = true
  override def hashCode: Int = 0

/** Has a companion `apply` that is not the constructor. */
final case class Trimmed(s: String)
object Trimmed:
  def apply(s: String, pad: Int): Trimmed = new Trimmed(s + pad.toString)
