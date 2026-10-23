package frflow
package lean

/** The open terms a Lean declaration takes, by name, in order: opaque types first, then parameters. */
final case class Ctx(opaques: List[String], params: List[String]):
  def ++(o: Ctx): Ctx = Ctx((opaques ++ o.opaques).distinct, (params ++ o.params).distinct)
  def names: List[String] = opaques ++ params
  def isEmpty: Boolean = names.isEmpty

object Ctx:
  val empty: Ctx = Ctx(Nil, Nil)
  def all(cs: Iterable[Ctx]): Ctx = cs.foldLeft(empty)(_ ++ _)

/** What some terms stand for in a statement instead of themselves (code, doing nothing, a value):
  * the Lean, with the open terms it mentions.
  */
type Env = Map[String, (String, Ctx)]
