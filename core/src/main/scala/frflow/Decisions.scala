package frflow

import frflow.Json.*

/** The developer's position on each node, computed from the snapshot and the ledger. Shared by
  * the CLI and the browser, so a decision is recorded the same way wherever it is made.
  *
  * A snapshot node carries `content` (what the developer sees and decides), its `hash`, its
  * `chain` (its hash together with its ancestors'), and the `code` it governs (a contract's
  * implementation, a design decision's files) with a fingerprint.
  *
  * States:
  *   - `proposed`: no decision yet (or rejected, then reworked);
  *   - `accepted`: decided, and nothing changed since;
  *   - `changed`: the node changed since it was decided (the diff shows how);
  *   - `parent-changed`: an ancestor changed since; the developer confirms it still holds;
  *   - `rejected`: an alternative was chosen instead; the agent removes it from the model.
  * A decided node that is no longer in the model is listed as `removed` until the developer
  * confirms the removal.
  */
object Decisions:
  private def s(j: Json, k: String): String = j(k).flatMap(_.str).getOrElse("")
  private def nodes(snapshot: Json): List[Json] = snapshot("nodes").map(_.arr.toList).getOrElse(Nil)
  private def byId(snapshot: Json): Map[String, Json] = nodes(snapshot).map(n => s(n, "id") -> n).toMap
  private def parentChain(snapshot: Json, n: Json): String =
    n("parent").flatMap(_.str).flatMap(byId(snapshot).get).fold("")(s(_, "chain"))

  def state(ledger: Ledger, n: Json, parentChain: String): String =
    ledger.current(s(n, "id")) match
      case Some(d) if d.action == "reject" || d.action == "remove" =>
        if d.action == "reject" && d.hash == s(n, "hash") then "rejected" else "proposed"
      case Some(d) if d.hash != s(n, "hash") => "changed"
      case Some(d) if d.chain != parentChain => "parent-changed"
      case Some(_)                           => "accepted"
      case None                              => "proposed"

  /** The snapshot with every node's state, decision history and kept alternatives, and the
    * decided nodes that are no longer in the model.
    */
  def annotate(snapshot: Json, ledger: Ledger): Json =
    val ids = byId(snapshot)
    def decisionJson(d: Decision) = obj(
      "action" -> str(d.action), "by" -> str(d.by), "at" -> str(d.at), "reason" -> str(d.reason), "content" -> d.content,
      "rejected" -> JArr(d.rejected.map(a => obj("id" -> str(a.id), "content" -> a.content))))
    val annotated = nodes(snapshot).map { n =>
      val id = s(n, "id")
      val st = state(ledger, n, parentChain(snapshot, n))
      val impl = n("code").flatMap(_("fingerprint")).flatMap(_.str)
      val decidedImpl = ledger.history(id).reverse.find(d => d.action == "accept" || d.action == "confirm").map(_.code)
      val fields = Seq(
        "state" -> str(st),
        "decision" -> ledger.history(id).reverse.find(d => d.action == "accept" || d.action == "confirm").fold(JNull)(decisionJson),
        "history" -> JArr(ledger.history(id).map(decisionJson)),
        "alternatives" -> JArr(ledger.rejected(id).map(a => obj("id" -> str(a.id), "content" -> a.content))),
        "codeChanged" -> JBool(st == "accepted" && impl.exists(i => decidedImpl.exists(_ != i))))
      JObj(n.obj.filterNot(f => fields.exists(_._1 == f._1)) ++ fields)
    }
    val removed = ledger.decisions.toList.sortBy(_._1).collect {
      case (id, ds) if !ids.contains(id) && ds.lastOption.exists(d => d.action == "accept" || d.action == "confirm") =>
        obj("id" -> str(id), "decision" -> decisionJson(ds.last))
    }
    JObj(snapshot.obj.filterNot(f => f._1 == "nodes" || f._1 == "removed") ++ Seq("nodes" -> JArr(annotated), "removed" -> JArr(removed)))

  /** A decision request, as the browser or the CLI sends it.
    *
    * @param action  `accept` (choose this node, rejecting `reject`), `confirm` (still valid after an
    *                ancestor or the implementation changed; with `subtree`, also every node below that
    *                waits for the same confirmation), or `remove` (agree that a decided node is gone)
    */
  final case class Request(action: String, node: String, by: String, reason: String, reject: List[String] = Nil, subtree: Boolean = false)

  /** Applies a decision; returns the new ledger and the events to record, or why it is refused. */
  def decide(snapshot: Json, ledger: Ledger, r: Request, at: String): Either[String, (Ledger, List[Json])] =
    val ids = byId(snapshot)
    def st(l: Ledger, id: String) = ids.get(id).fold("removed")(n => state(l, n, parentChain(snapshot, n)))
    def event(action: String, id: String, extra: (String, Json)*) =
      obj((Seq("at" -> str(at), "action" -> str(action), "node" -> str(id), "by" -> str(r.by), "reason" -> str(r.reason)) ++ extra)*)
    def make(action: String, n: Json, rejected: List[Alternative]) =
      Decision(action, n("content").getOrElse(JNull), parentChain(snapshot, n), r.by, at, r.reason, rejected,
        n("code").flatMap(_("fingerprint")).flatMap(_.str).getOrElse(""))
    if r.by.trim.isEmpty then return Left("say who decides")
    if r.reason.trim.isEmpty then return Left("give the reason for the decision: it is kept as part of the theory")
    r.action match
      case "remove" =>
        if ids.contains(r.node) then Left(s"${r.node} is still in the model")
        else ledger.history(r.node).lastOption match
          case Some(last) if last.action == "accept" || last.action == "confirm" =>
            Right((ledger.add(r.node, last.copy(action = "remove", by = r.by, at = at, reason = r.reason, rejected = Nil)), List(event("remove", r.node))))
          case _ => Left(s"${r.node} has no decision to remove")
      case "accept" | "confirm" if !ids.contains(r.node) => Left(s"unknown node ${r.node}")
      case "accept" | "confirm" =>
        val n = ids(r.node)
        val parent = n("parent").flatMap(_.str)
        if parent.exists(p => st(ledger, p) != "accepted") then return Left(s"decide ${parent.get} first: the tree is decided from the root down")
        if r.action == "accept" then
          val bad = r.reject.filter(x => x == r.node || !ids.get(x).exists(_("parent").flatMap(_.str) == parent))
          if bad.nonEmpty then return Left(s"not an alternative to ${r.node}: ${bad.mkString(", ")}")
          val rejected = r.reject.map(x => Alternative(x, ids(x)("content").getOrElse(JNull)))
          val l1 = ledger.add(r.node, make("accept", n, rejected))
          val l2 = r.reject.foldLeft(l1)((l, x) => l.add(x, make("reject", ids(x), Nil).copy(reason = s"${r.node} was chosen: ${r.reason}")))
          Right((l2, event("accept", r.node, "rejected" -> JArr(r.reject.map(str))) :: r.reject.map(x => event("reject", x))))
        else
          val here = st(ledger, r.node)
          val implChanged = annotate(snapshot, ledger)("nodes").get.arr.find(x => s(x, "id") == r.node).exists(_("codeChanged").contains(JBool(true)))
          if here != "parent-changed" && !implChanged && !r.subtree then
            return Left(s"${r.node} is $here: only a node whose ancestor or code changed is confirmed")
          val first = if here == "parent-changed" || implChanged then List(r.node) else Nil
          // below the node, in tree order: each confirmation changes nothing above it, so states stay valid
          def below(id: String): List[String] = nodes(snapshot).filter(_("parent").flatMap(_.str).contains(id)).flatMap(c => s(c, "id") :: below(s(c, "id")))
          val targets = first ++ (if r.subtree then below(r.node) else Nil)
          targets.foldLeft[Either[String, (Ledger, List[Json])]](Right((ledger, Nil))) {
            case (Right((l, evs)), id) =>
              if st(l, id) == "parent-changed" || id == r.node then
                Right((l.add(id, make("confirm", ids(id), Nil)), evs :+ event("confirm", id)))
              else Right((l, evs))
            case (left, _) => left
          }
      case other => Left(s"unknown action $other")
