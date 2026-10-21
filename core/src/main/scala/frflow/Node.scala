package frflow

/** A concrete behaviour of a node: a start state and steps `(event, next state)`.
  * The developer states whether the node must allow it or must forbid it.
  */
final case class Scenario[S, E](name: String, expectAllowed: Boolean, start: S, steps: List[(E, S)])

def allowed[S, E](name: String, start: S, steps: (E, S)*): Scenario[S, E] = Scenario(name, true, start, steps.toList)
def forbidden[S, E](name: String, start: S, steps: (E, S)*): Scenario[S, E] = Scenario(name, false, start, steps.toList)

/** How a node specializes its parent: its states map to parent states (`abs`),
  * and each of its events is a parent event or, for `None`, changes nothing the
  * parent sees (`event`).
  */
final class ParentLink[S, E](val node: Node[?, ?], val abs: Lifted[S => Any], val event: Lifted[(S, E) => Option[Any]])

/** A node of the knowledge base: a system with states `S` and events `E`.
  *
  *   - `init`: the initial states;
  *   - `next(s, e, t)`: event `e` may take state `s` to state `t`;
  *   - `property`: holds in every reachable state. The root's property is the root theorem.
  *
  * A child node is proven to specialize its parent: every behaviour of the
  * child is a behaviour of the parent. The root theorem therefore holds in
  * every node.
  */
final class Node[S, E] @scala.annotation.publicInBinary private[frflow] (
    val id: String,
    val statement: String,
    val init: Lifted[S => Boolean],
    val next: Lifted[(S, E, S) => Boolean],
    val property: Lifted[S => Boolean],
    val parent: Option[ParentLink[S, E]],
    val scenarios: List[Scenario[S, E]]
):
  def isRoot: Boolean = parent.isEmpty
  def stateType: String = init.params.head._2
  def eventType: String = next.params(1)._2

  /** Every lifted expression of the node. */
  def lifted: List[Lifted[?]] = List(init, next, property) ++ parent.toList.flatMap(l => List(l.abs, l.event))

  /** Adds scenarios: behaviours the node must allow or forbid. */
  def withScenarios(more: Scenario[S, E]*): Node[S, E] =
    Node(id, statement, init, next, property, parent, scenarios ++ more)

  /** Adds a property of this node (an invariant), proven like the root theorem. */
  inline def withProperty(inline p: S => Boolean): Node[S, E] =
    Node(id, statement, init, next, Lifted(p), parent, scenarios)

  /** A child node that specializes this one. */
  inline def refine[C, CE](id: String, statement: String)(
      inline init: C => Boolean,
      inline next: (C, CE, C) => Boolean,
      inline abs: C => S,
      inline event: (C, CE) => Option[E]
  ): Node[C, CE] =
    Node(id, statement, Lifted(init), Lifted(next), Lifted((_: C) => true), Some(ParentLink(this, Lifted(abs), Lifted(event))), Nil)

  override def toString: String = id

object Node:
  /** The root of a knowledge base: the formal statement of the project's idea. */
  inline def root[S, E](id: String, statement: String)(
      inline init: S => Boolean,
      inline next: (S, E, S) => Boolean,
      inline theorem: S => Boolean
  ): Node[S, E] =
    Node(id, statement, Lifted(init), Lifted(next), Lifted(theorem), None, Nil)

/** A project: the idea (a Markdown file written by the developer) and the nodes
  * derived from it. `name` is the Lean namespace.
  */
class Project(val name: String, val idea: String, nodeList: Node[?, ?]*):
  val nodes: List[Node[?, ?]] = nodeList.toList

  def node(id: String): Option[Node[?, ?]] = nodes.find(_.id == id)
  def root: Node[?, ?] = nodes.find(_.isRoot).getOrElse(throw IllegalStateException("no root node"))
  def parentOf(n: Node[?, ?]): Option[Node[?, ?]] = n.parent.map(_.node)
  def children(n: Node[?, ?]): List[Node[?, ?]] = nodes.filter(c => parentOf(c).contains(n))

  /** The node and its ancestors, root first. */
  def path(n: Node[?, ?]): List[Node[?, ?]] = parentOf(n).fold(List(n))(p => path(p) :+ n)

  /** Nodes with every parent before its children. */
  def ordered: List[Node[?, ?]] = nodes.sortBy(path(_).size)

  /** Theory functions used anywhere, dependencies first. */
  def defs: List[Def[?]] =
    val out = scala.collection.mutable.LinkedHashMap.empty[String, Def[?]]
    val visiting = scala.collection.mutable.Set.empty[String]
    def visit(d: Def[?]): Unit =
      if !out.contains(d.name) && !visiting(d.name) then
        visiting += d.name
        d.lifted.defs.foreach(visit)
        visiting -= d.name
        out(d.name) = d
    nodes.flatMap(_.lifted).flatMap(_.defs).foreach(visit)
    out.values.toList

  /** Domain types used anywhere, dependencies first. */
  def types: List[TypeDecl] =
    val all = (nodes.flatMap(_.lifted) ++ defs.map(_.lifted)).flatMap(_.types)
    val byName = all.groupBy(_.name).view.mapValues(_.head).toMap
    val out = scala.collection.mutable.LinkedHashMap.empty[String, TypeDecl]
    def visit(n: String): Unit =
      if !out.contains(n) then byName.get(n).foreach { d => d.uses.foreach(visit); out(n) = d }
    all.map(_.name).distinct.foreach(visit)
    out.values.toList

  /** Structural problems; a project with problems is not checked. */
  def problems: List[String] =
    val ids = nodes.map(_.id)
    val names = types.map(_.name) ++ defs.map(_.name)
    val Ident = """[A-Za-z_][A-Za-z0-9_]*""".r
    List(
      ids.diff(ids.distinct).distinct.map(d => s"duplicate node id $d"),
      ids.filterNot(Ident.matches).map(i => s"node id $i is not an identifier"),
      if nodes.count(_.isRoot) != 1 then List(s"exactly one root node is required, found ${nodes.count(_.isRoot)}") else Nil,
      nodes.flatMap(n => parentOf(n).filterNot(nodes.contains).map(p => s"${n.id}: parent ${p.id} is not in the project")),
      ids.filter(names.contains).map(i => s"node id $i clashes with a type or function of the same name"),
      nodes.filter(_.statement.trim.isEmpty).map(n => s"${n.id}: empty statement"),
      (nodes.flatMap(_.lifted) ++ defs.map(_.lifted)).flatMap(_.types).groupBy(_.name).collect {
        case (n, ds) if ds.map(_.lean).distinct.size > 1 => s"two different Scala types are named $n"
      }.toList
    ).flatten
