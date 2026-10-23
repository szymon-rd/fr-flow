package frflow
package ledger

import frflow.protocol.*
import io.circe.Json

/** Snapshots written by hand, for the pure tests: a root `R`, its part `A`, and `A`'s part `B`. */
object Dag:
  def str(s: String): Json = Json.fromString(s)
  private def strs(xs: List[String]): Json = Json.fromValues(xs.map(str))

  def node(id: String, statement: String, parents: List[String] = Nil, parts: List[String] = Nil,
      kind: NodeKind = NodeKind.Claim, extra: List[(String, Json)] = Nil): SnapNode =
    val c = Content((List("kind" -> str(kind.toString), "parents" -> strs(parents), "parts" -> strs(parts),
      "statement" -> str(statement)) ++ extra)*)
    SnapNode(NodeId(id), kind, c, c.hash, parents = parents.map(NodeId(_)), parts = parts.map(NodeId(_)))

  /** The node with its content changed as `f` says (and its hash with it). */
  def changed(n: SnapNode)(f: PartialFunction[(String, Json), (String, Json)]): SnapNode =
    val c = n.content.mapFields(f)
    n.copy(content = c, hash = c.hash)

  def restated(n: SnapNode, statement: String): SnapNode = changed(n) { case ("statement", _) => "statement" -> str(statement) }

  val r: SnapNode = node("R", "Readers find the books they ask for.", parts = List("A"))
  val a: SnapNode = node("A", "Every book asked for is on a shelf.", parents = List("R"), parts = List("B"))
  val b: SnapNode = node("B", "Each shelf lists its books.", parents = List("A"))
  val shelf: Snapshot = snap(r, a, b)

  def snap(ns: SnapNode*): Snapshot = Snapshot("Shelf", ns.toList)
  /** The snapshot with the node of the same id replaced. */
  def replacing(s: Snapshot, n: SnapNode): Snapshot = s.copy(nodes = s.nodes.map(m => if m.id == n.id then n else m))

  def id(s: String): NodeId = NodeId(s)
  def ids(xs: String*): List[NodeId] = xs.map(NodeId(_)).toList
  def stamp(i: Int): Stamp = Stamp(f"2026-01-01T00:00:$i%02dZ")

  def req(node: String, reason: String = "", reject: List[String] = Nil, revisit: List[String] = Nil,
      confirm: List[String] = Nil, by: String = "dev", action: Action = Action.Accept, seen: Option[String] = None) =
    DecisionRequest(NodeId(node), by, if reason.isEmpty then s"$node holds for this reason" else reason, ids(reject*),
      ids(revisit*), ids(confirm*), action, seen)

  def right[A](e: Either[Refusal, A]): A = e.fold(r => throw AssertionError(r.message), identity)

  /** Every node of `s` accepted, in order. */
  def acceptAll(s: Snapshot, from: Ledger = Ledger.empty, start: Int = 1): Ledger =
    Decisions.order(s).zipWithIndex.foldLeft(from)((l, x) => right(Decide(s, l, req(x._1.value), stamp(start + x._2))))
