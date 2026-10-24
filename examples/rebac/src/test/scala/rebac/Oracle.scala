package rebac

import scala.collection.mutable

/** What a check should answer, written from IDEA.md alone, not from the service's code or its FrFlow model (adapted from
  * the QA run's oracle): version v is what the first v writes leave (adding a held tuple or deleting an absent one changes
  * nothing); a relation's rules are its own tuples (a userset subject counts its members), the relation it is implied by,
  * and the relation inherited through a link; one rule is one step, and what needs more steps than the depth is no.
  */
final class Oracle(schema: List[RelationDef], depth: Int):
  private val rules: Map[(String, String), List[Rule]] =
    schema.foldLeft(Map.empty[(String, String), List[Rule]])((m, d) => if m.contains((d.kind, d.rel)) then m else m.updated((d.kind, d.rel), d.rules))
  private val log = mutable.ArrayBuffer.empty[(Boolean, RelTuple)]

  def write(add: Boolean, t: RelTuple): Int = { log += (add -> t); log.size }
  def latest: Int = log.size

  def tuplesAt(v: Int): List[RelTuple] =
    log.take(v).foldLeft(Vector.empty[RelTuple]) { case (ts, (add, t)) =>
      if add then (if ts.contains(t) then ts else ts :+ t) else ts.filterNot(_ == t)
    }.toList

  def allowed(o: Obj, rel: String, person: String, v: Int): Boolean =
    val byObjRel = tuplesAt(v).groupBy(t => (t.obj, t.rel))
    val memo = mutable.HashMap.empty[(Int, Obj, String), Boolean]
    def within(k: Int, o: Obj, r: String): Boolean =
      k > 0 && memo.getOrElseUpdate((k, o, r), rules.getOrElse((o.kind, r), Nil).exists {
        case Rule.Direct => byObjRel.getOrElse((o, r), Nil).exists(_.subject match
          case Subject.Person(p)       => p == person
          case Subject.Members(g, gr)  => within(k - 1, g, gr)
          case Subject.Link(_)         => false)
        case Rule.Implied(by) => within(k - 1, o, by)
        case Rule.Inherited(link, via) => byObjRel.getOrElse((o, link), Nil).exists(_.subject match
          case Subject.Link(parent) => within(k - 1, parent, via)
          case _                    => false)
      })
    within(depth, o, rel)
