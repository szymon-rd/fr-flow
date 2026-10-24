package rebac

import scala.collection.mutable

/** The check as the service runs it: `resolve` (Checks.scala) step for step, with each step's answer remembered within
  * one check. For one check the version and the person are fixed, so whether `(object, relation)` is reached within `k`
  * steps depends on those three only; remembering it keeps a cycle of groups, or a wide fan-out, to one visit per
  * `(steps left, object, relation)` instead of one per path. Plain code: CheckContract's code is the proven `resolveCheck`,
  * and this runs beside it, checked against it on the examples and on generated data.
  */
final class Resolution(tuplesOf: (Int, Obj) => List[RelTuple], rulesFor: (String, String) => List[Rule]):
  def allowed(q: Query, v: Int, depth: Int): Boolean =
    val seen = mutable.HashMap.empty[(Int, Obj, String), Boolean]
    def within(k: Int, o: Obj, r: String): Boolean =
      k > 0 && seen.getOrElseUpdate((k, o, r), rulesFor(o.kind, r).exists {
        case Rule.Direct => tuplesOf(v, o).exists(t => t.rel == r && (t.subject match
          case Subject.Person(id)     => id == q.person
          case Subject.Members(g, gr) => within(k - 1, g, gr)
          case Subject.Link(_)        => false))
        case Rule.Implied(by) => within(k - 1, o, by)
        case Rule.Inherited(link, via) => tuplesOf(v, o).exists(t => t.rel == link && (t.subject match
          case Subject.Link(parent) => within(k - 1, parent, via)
          case _                    => false))
      })
    within(depth, q.obj, q.rel)
