package frflow.model

/** A fragment of Lean source. Inside node models the following names are bound:
  *   - `s`: the current state of the node (in guards, actions, invariants, init, abs, glue, witnesses)
  *   - `p`: the parameters of the event (in guards, actions, witnesses)
  * Expressions may refer to vocabulary types, to the node's own definitions, and
  * to ancestor definitions by their node id (for example `T0.Entry`).
  */
final case class LeanExpr(text: String):
  override def toString: String = text

/** A shared concept of a theory. Defined once and imported by every node. */
sealed trait VocabEntry:
  def name: String
  def doc: String

object VocabEntry:
  /** A type whose structure is deliberately not specified. */
  final case class Opaque(name: String, doc: String) extends VocabEntry

  /** A type defined as an existing Lean type. */
  final case class Alias(name: String, lean: LeanExpr, doc: String) extends VocabEntry

/** An environment assumption. Assumptions are never proven inside the node that
  * uses them: they appear as `assume` clauses of event guards, which restrict the
  * environment's behaviour, as opposed to `check` clauses, which the implementation
  * must enforce.
  */
final case class Assumption(id: String, name: String, statement: String, justification: String)

final case class Field(name: String, tpe: LeanExpr, doc: String = "")

final case class AssumeClause(assumptionId: String, expr: LeanExpr)

/** How an event relates to the parent node. */
enum EventTarget:
  /** Only valid on the root node. */
  case Unspecified

  /** Refines the named parent event. `witness` builds the parent event's parameters
    * from `s` and `p` of this event.
    */
  case Refines(parentEvent: String, witness: LeanExpr)

  /** A new event that leaves the abstract (parent) state unchanged. */
  case Skip

final case class EventDef(
    name: String,
    parameters: Seq[Field] = Nil,
    assumes: Seq[AssumeClause] = Nil,
    checks: Seq[LeanExpr] = Nil,
    action: Option[LeanExpr] = None,
    target: EventTarget = EventTarget.Unspecified,
    description: String = ""
)

final case class InvariantDef(name: String, expr: LeanExpr, doc: String = "")

/** Link of a node to its parent: abstraction function and gluing invariant. */
final case class Link(abs: LeanExpr, glue: Option[LeanExpr])

final case class NodeSpec(
    defs: Seq[LeanExpr] = Nil,
    state: Seq[Field] = Nil,
    init: LeanExpr = LeanExpr("True"),
    events: Seq[EventDef] = Nil,
    invariants: Seq[InvariantDef] = Nil
)

final case class Node(
    id: String,
    name: String,
    statement: String,
    rationale: String,
    parent: Option[String],
    link: Option[Link],
    spec: NodeSpec
):
  def isRoot: Boolean = parent.isEmpty
  def event(name: String): Option[EventDef] = spec.events.find(_.name == name)

final case class TheoryModel(
    name: String,
    vocabulary: Seq[VocabEntry],
    assumptions: Seq[Assumption],
    nodes: Seq[Node]
):
  private lazy val byId: Map[String, Node] = nodes.map(n => n.id -> n).toMap

  def node(id: String): Option[Node] = byId.get(id)
  def nodeOrFail(id: String): Node =
    byId.getOrElse(id, throw new NoSuchElementException(s"Unknown node '$id' in theory '$name'"))
  def roots: Seq[Node] = nodes.filter(_.isRoot)
  def children(id: String): Seq[Node] = nodes.filter(_.parent.contains(id))
  def parentOf(n: Node): Option[Node] = n.parent.flatMap(byId.get)
  def assumption(id: String): Option[Assumption] = assumptions.find(_.id == id)

  /** Ancestors from the direct parent up to the root. */
  def ancestors(n: Node): List[Node] =
    def loop(cur: Node, seen: Set[String]): List[Node] =
      parentOf(cur) match
        case Some(p) if !seen(p.id) => p :: loop(p, seen + p.id)
        case _                      => Nil
    loop(n, Set(n.id))

  /** Path from the root down to `n`, inclusive. */
  def pathFromRoot(n: Node): List[Node] = (n :: ancestors(n)).reverse

  /** Nodes ordered so that every parent precedes its children. */
  def topological: Seq[Node] =
    nodes.sortBy(n => ancestors(n).size)
