package frflow
package ledger

import frflow.protocol.*
import io.circe.Json
import java.time.Instant

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
  def replacing(s: Snapshot, n: SnapNode): Snapshot = s.copy(nodes = s.nodes.map(m => if m.id == n.id then n else m))

  def id(s: String): NodeId = NodeId(s)
  def ids(xs: String*): List[NodeId] = xs.map(NodeId(_)).toList
  def stamp(i: Int): Stamp = Stamp(Instant.parse(f"2026-01-01T00:00:$i%02dZ"))

  /** Accepting `node`, for a reason of its own unless one is given. */
  def accept(node: String, reason: String = "", revisit: List[String] = Nil, seen: Option[String] = None): Decide =
    Decide.Accept(ids(node), if reason.isEmpty then s"$node holds for this reason" else reason, ids(revisit*), seen.map(id(node) -> _).toMap)

  /** `l` with R accepted as it is in `s`, and nothing else decided again. */
  def onlyRoot(s: Snapshot, l: Ledger): Ledger =
    l.add(id("R"), Decision(Action.Accept, "dev", stamp(30).at, "R holds for this reason", content = s.nodes.find(_.id == id("R")).fold(Content.empty)(_.content)))

  def right[A](e: Either[Refusal, A]): A = e.fold(r => throw AssertionError(r.message), identity)

  def acceptAll(s: Snapshot, from: Ledger = Ledger.empty, start: Int = 1): Ledger =
    Graph(s).order.zipWithIndex.foldLeft(from)((l, x) => right(Decide(s, l, accept(x._1.value), "dev", stamp(start + x._2))))
