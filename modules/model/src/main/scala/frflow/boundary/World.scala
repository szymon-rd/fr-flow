package frflow
package boundary

import frflow.types.Shape

/** The states of the boundaries' models, before or after a flow runs: `before(DatabaseModel)`. */
/** `faults`: which calls of the failing boundaries fail, in order (`true`: that call fails; when the list runs out,
  * none does). They are the outside's, not a model's state: two worlds whose models hold the same are equal.
  */
final class World private[frflow] (private[frflow] val parts: Map[StateModel[?], Any], val faults: List[Boolean] = Nil):
  def apply[S](m: StateModel[S]): S = parts(m).asInstanceOf[S]
  private[frflow] def updated(m: StateModel[?], s: Any): World = new World(parts.updated(m, s), faults)
  /** The same world, where the next calls of failing boundaries fail as `fs` says: `w.failing(false, true)`, the
    * second call fails.
    */
  def failing(fs: Boolean*): World = new World(parts, fs.toList)
  private[frflow] def withFaults(fs: List[Boolean]): World = new World(parts, fs)
  override def equals(o: Any): Boolean = o match { case w: World => w.parts == parts; case _ => false }
  override def hashCode: Int = parts.hashCode
  override def toString: String =
    (parts.map((m, s) => s"${m.lean} = ${Example.show(s)}") ++ Option.when(faults.nonEmpty)(s"faults = ${faults.mkString("[", ", ", "]")}"))
      .mkString("World(", ", ", ")")

object World:
  def apply(parts: (StateModel[?], Any)*): World = new World(parts.toMap)
  given LeanType[World] = LeanType.of(Shape.WorldT)
  extension (w: Term[World])
    def apply[S](m: StateModel[S]): Term[S] = Term(Tree.Part(w.termTree, m), m.stateType)
