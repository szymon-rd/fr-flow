package frflow.cli.text

import cats.kernel.Monoid
import frflow.core.name.NodeId

/** What layers on top add to FrFlow's views of a project, made for one style: the nodes they hold back from the
  * developer's queue (`aside`), a word shown beside a node, warnings `status` and `ci` fail on, phrases for the
  * summary's "Waiting:" line, sections closing the inbox (a title and its lines), and lines closing a node's `show`.
  * A monoid: each layer's added to the others'.
  */
final case class Contribution(aside: Set[NodeId], marks: Map[NodeId, String], warnings: List[String],
    waiting: List[String], inbox: List[(String, List[String])], node: NodeId => List[String])

object Contribution:
  val empty: Contribution = Contribution(Set.empty, Map.empty, Nil, Nil, Nil, _ => Nil)

  given Monoid[Contribution] = Monoid.instance(empty, (a, b) =>
    Contribution(a.aside ++ b.aside, a.marks ++ b.marks, a.warnings ++ b.warnings, a.waiting ++ b.waiting,
      a.inbox ++ b.inbox, id => a.node(id) ++ b.node(id)))
