package frflow.cli

import frflow.protocol.NodeId

/** What layers add to a view: the nodes they hold back from the developer's queue (`aside`), a word shown beside a node
  * (`marks`), warnings `status` and `ci` fail on, phrases for the summary's "Waiting:" line, sections closing the inbox,
  * lines closing a node's `show`, and keys for the review.
  */
final case class Contribution(aside: Set[NodeId] = Set.empty, marks: Map[NodeId, String] = Map.empty,
    warnings: List[String] = Nil, waiting: Style => List[String] = _ => Nil, inbox: Style => List[String] = _ => Nil,
    node: (NodeId, Style) => List[String] = (_, _) => Nil, review: List[ReviewKey] = Nil):
  def ++(o: Contribution): Contribution =
    Contribution(aside ++ o.aside, marks ++ o.marks, warnings ++ o.warnings, st => waiting(st) ++ o.waiting(st),
      st => inbox(st) ++ o.inbox(st), (id, st) => node(id, st) ++ o.node(id, st), review ++ o.review)

object Contribution:
  val empty: Contribution = Contribution()
  def all(cs: List[Contribution]): Contribution = cs.foldLeft(empty)(_ ++ _)
