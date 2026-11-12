package frflow.core.analysis.resolution

import frflow.core.graph.Walk
import frflow.core.name.{NodeId, SymbolName}
import frflow.core.Theory

/** What each node's proof of its code relies on (`Resolve.reliesOn`), a claim about other code left out where it
  * would close a circle. A node checked against code relies on every statement constraining a Definition the code
  * calls, through the defines the statement calls, so a statement about other code can be among them though no proof
  * needs it: a claim about `handle` mentions a word `housekeep` calls, a claim about `housekeep` a word `handle`
  * calls, and each would rest on the other. A claim is about other code when it constrains a function with code that
  * the code checked does not reach. Taking the nodes and what each relies on in the
  * theory's order, such a claim is kept unless what it rests on reaches back to the node; a theory with no circle
  * keeps every one. A circle that remains, through parts or claims about what the code calls, rests on itself
  * (`Resolve.circles`).
  */
object Relying:
  def of(t: Theory): Map[NodeId, List[NodeId]] =
    val ids = t.nodes.map(_.node.id)
    val raw = ids.map(id => id -> Resolve.reliesOn(t, id)).toMap
    val fixed = ids.map(id => id -> fromParts(t, id)).toMap
    def below(relies: Map[NodeId, List[NodeId]])(id: NodeId): List[NodeId] =
      fixed(id).getOrElse(relies.getOrElse(id, Nil))
    if Resolve.circling(ids, below(raw)).isEmpty then raw
    else
      val other = ids.map(id => id -> aboutOtherCode(t, id, raw(id))).toMap
      val kept = ids.foldLeft(ids.map(id => id -> raw(id).filterNot(other(id))).toMap) { (relies, id) =>
        raw(id).filter(other(id)).foldLeft(relies) { (r, m) =>
          if Walk.breadthFirst(List(m), identity)(below(r)).contains(id) then r else r.updated(id, r(id) :+ m)
        }
      }
      ids.map(id => id -> raw(id).filter(kept(id).contains)).toMap

  /** What a node is proven from when that is its parts, not what its code relies on (`Resolve.provenFrom`). */
  private def fromParts(t: Theory, id: NodeId): Option[List[NodeId]] =
    val parts = t.refinement.parts(id)
    if SaysWhat.checkedAgainst(t, id).isEmpty then Some(parts)
    else Some(parts.filter(p => t.node(p).exists(_.statement.stated))).filter(_.nonEmpty)

  /** Of what a node relies on, the claims about code its own does not reach. */
  private def aboutOtherCode(t: Theory, id: NodeId, relies: List[NodeId]): Set[NodeId] =
    SaysWhat.checkedAgainst(t, id).fold(Set.empty[NodeId]) { c =>
      val reached: Set[SymbolName] = (Callees.reaching(t, c.calls.symbols) ++ c.standsFor.keys).toSet
      relies.filter(m => Constrained.of(t, m).exists(s => Constrained.isFunction(t, s) &&
        t.code.attached.contains(s) && !reached(s))).toSet
    }
