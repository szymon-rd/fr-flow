package frflow

import frflow.Json.*
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path}

/** Result of one obligation: `proven`, `open` or `failed`. */
final case class Result(name: String, status: String, detail: String = "")

/** The outcome of checking one node. `status` is `proven`, `open`, `failed`,
  * `model-error` or `waiting` (proven, but its parent is not yet).
  */
final case class NodeCheck(
    hash: String,
    status: String,
    obligations: List[Result],
    messages: List[String],
    axioms: List[String],
    at: String
)

/** A decision of the developer about a node.
  *
  * @param action   `accept` (the developer chose the node, as seen), `confirm`
  *                 (it still holds after something above it moved), `reject` (an alternative not
  *                 chosen, as it was proposed), `revisit` (the developer said a change above may affect
  *                 it, so it is reviewed again), `remove` (the developer agreed that a decided node is
  *                 gone), `migrate` (a new FrFlow recorded the same decision in a new shape) or
  *                 `acknowledge` (of the ledger itself: a restart or a rewrite)
  * @param content  the node as the developer saw it; the decision is bound to its hash
  * @param chain    the content of the ancestors, as decided; when it changes, the node is reviewed
  * @param reason   why: kept as part of the theory
  * @param rejected for `accept`, the alternatives rejected by this choice
  * @param code     the fingerprint of the source files the node governs, when decided
  * @param held     the decisions below that were shown with this one and left as they are:
  *                 considered, and still holding
  * @param after    the node's decision this one follows (its `ref`): two decisions following the same
  *                 one come from two branches, merged; the node is then decided again
  * @param commit   the git commit checked out when deciding
  * @param tree     the code as decided, written to git as a tree, to show how the code changed since
  *                 (a clone without it falls back to `commit`)
  */
final case class Decision(action: String, content: Json, chain: String, by: String, at: String, reason: String,
    rejected: List[String] = Nil, code: String = "", commit: String = "", tree: String = "", held: List[String] = Nil,
    after: String = "", key: String = "", sig: String = ""):
  def hash: String = Decision.hash(content)
  /** The decision without its signature: what is signed, and what a rewrite is judged on. */
  def unsigned: Decision = copy(key = "", sig = "")

object Decision:
  /** The hash a decision is bound to. Runs of whitespace count as one space, so reformatting
    * changes nothing that was decided.
    */
  def hash(content: Json): String =
    java.security.MessageDigest.getInstance("SHA-256").digest(normal(content).compact.getBytes(UTF_8)).map("%02x".format(_)).mkString

  private def normal(j: Json): Json = j match
    case JStr(s)  => JStr(s.trim.replaceAll("\\s+", " "))
    case JArr(xs) => JArr(xs.map(normal))
    case JObj(fs) => JObj(fs.map((k, v) => k -> normal(v)))
    case other    => other

/** The developer's decisions, per node, oldest first: the record of the theory and its history.
  * Kept in `.frflow/ledger.json` and committed. Nothing in it is ever overwritten.
  */
final case class Ledger(decisions: Map[String, List[Decision]]):
  def history(id: String): List[Decision] = decisions.getOrElse(id, Nil)
  def current(id: String): Option[Decision] = history(id).lastOption
  /** The developer's choice of the node: the acceptance that chose it (the first since it was last
    * rejected or removed), which carries the reason it was chosen. Later acceptances are of changes.
    */
  def chosen(id: String): Option[Decision] =
    history(id).reverse.takeWhile(d => d.action != "reject" && d.action != "remove").reverse
      .find(_.action == "accept")
  /** What the node is bound to now: its last acceptance or confirmation (also while the developer
    * has asked to revisit it).
    */
  def binding(id: String): Option[Decision] = current(id) match
    case Some(d) if d.action == "revisit" => history(id).reverse.find(x => Ledger.binds(x.action))
    case c => c.filter(d => Ledger.binds(d.action))

  def add(id: String, d: Decision): Ledger =
    Ledger(decisions.updated(id, history(id) :+ d.copy(after = current(id).fold("")(Ledger.entry))))

  /** Two branches decided the node, and the merge kept both: the last decision is one of two that
    * follow the same one. Nothing says which holds, so the node is decided again.
    */
  def forked(id: String): Boolean =
    current(id).exists(d => d.after.nonEmpty && history(id).count(_.after == d.after) > 1)

  /** The alternatives ever rejected in favour of a node, as they were proposed. */
  def alternatives(id: String): List[(String, Json)] =
    history(id).filter(_.action == "accept").flatMap(_.rejected).distinct
      .flatMap(r => history(r).reverse.find(_.action == "reject").map(d => r -> d.content))

  /** The nodes rejected under `parent` (now or once), each with its content and the reason: the
    * options already turned down where a new proposal stands.
    */
  def rejectedUnder(parent: String): List[(String, Json, String)] =
    decisions.toList.sortBy(_._1).flatMap((id, ds) => ds.lastOption.filter(d => d.action == "reject" &&
      d.content("parent").flatMap(_.str).contains(parent)).map(d => (id, d.content, d.reason)))

  /** The decisions where `id` was shown and left as it is (considered, still holding). */
  def considered(id: String): List[(String, Decision)] = all.filter(_._2.held.contains(id))

  /** Restart commits the developer acknowledged. */
  def acknowledged: Set[String] = history(Ledger.Self).filter(_.action == "acknowledge").map(_.commit).toSet

  /** Every decision, newest first. */
  def all: List[(String, Decision)] = decisions.toList.flatMap((id, ds) => ds.map(id -> _)).sortBy(_._2.at).reverse

  /** Content already recorded for the node is written once, then referred to by its hash
    * ("content": "same:<hash>"), which stays right when a merge interleaves two branches' decisions.
    */
  def toJson: Json =
    obj("decisions" -> JObj(decisions.toSeq.sortBy(_._1).map { (id, ds) =>
      id -> JArr(ds.zipWithIndex.map((d, i) => JObj(Seq(
        "action" -> str(d.action), "by" -> str(d.by), "at" -> str(d.at), "reason" -> str(d.reason)) ++
        (if d.rejected.isEmpty then Nil else Seq("rejected" -> JArr(d.rejected.map(str)))) ++
        (if d.held.isEmpty then Nil else Seq("held" -> JArr(d.held.map(str)))) ++
        (if d.after.isEmpty then Nil else Seq("after" -> str(d.after))) ++
        (if d.code.isEmpty then Nil else Seq("code" -> str(d.code))) ++
        (if d.commit.isEmpty then Nil else Seq("commit" -> str(d.commit))) ++
        (if d.tree.isEmpty then Nil else Seq("tree" -> str(d.tree))) ++
        (if d.sig.isEmpty then Nil else Seq("key" -> str(d.key), "sig" -> str(d.sig))) ++
        Seq("chain" -> str(d.chain), "content" -> (if ds.take(i).exists(_.content == d.content) then str("same:" + Ledger.ref(d.content)) else d.content)))))
    }))

object Ledger:
  val empty: Ledger = Ledger(Map.empty)

  /** Two branches' ledgers merged: every decision of either, each node's in order (this side's,
    * then the other's that this one lacks). Nothing is dropped, so the merge passes `rewrites`; a
    * node both sides decided is `forked`, and decided again. Git's merge driver for the ledger.
    */
  def merge(ours: Ledger, theirs: Ledger): Ledger =
    Ledger((ours.decisions.keySet ++ theirs.decisions.keySet).toList.map { id =>
      val mine = ours.history(id)
      val seen = mine.map(entry).toSet
      id -> (mine ++ theirs.history(id).filterNot(d => seen(entry(d))))
    }.toMap)

  /** Actions a node is bound to: the developer's acceptance or confirmation, or the agent settling
    * a mechanical node.
    */
  def binds(action: String): Boolean = Set("accept", "confirm", "migrate")(action)

  /** A short reference to a decision: what was decided, by whom, when and why. */
  private[frflow] def entry(d: Decision): String =
    java.security.MessageDigest.getInstance("SHA-256")
      .digest(Seq(d.action, d.by, d.at, d.reason, ref(d.content)).mkString("\u0000").getBytes(UTF_8)).take(8).map("%02x".format(_)).mkString

  /** A short reference to a content exactly as recorded. */
  private[frflow] def ref(content: Json): String =
    java.security.MessageDigest.getInstance("SHA-256").digest(content.compact.getBytes(UTF_8)).take(8).map("%02x".format(_)).mkString

  def load(file: Path): Ledger =
    if !Files.isRegularFile(file) then empty else fromJson(Json.parse(Files.readString(file, UTF_8)))

  def save(file: Path, l: Ledger): Unit =
    Option(file.toAbsolutePath.getParent).foreach(Files.createDirectories(_))
    Files.writeString(file, l.toJson.render() + "\n", UTF_8)

  private def s(j: Json, k: String): String = j(k).flatMap(_.str).getOrElse("")

  def fromJson(j: Json): Ledger =
    Ledger(j("decisions").map(_.obj).getOrElse(Nil).map { (id, ds) =>
      id -> ds.arr.foldLeft(List.empty[Decision]) { (acc, d) =>
        val content = d("content") match
          case Some(JStr("same")) => acc.lastOption.fold(JNull)(_.content) // the earlier form: the previous entry's
          case Some(JStr(ref)) if ref.startsWith("same:") =>
            acc.reverse.find(x => Ledger.ref(x.content) == ref.stripPrefix("same:")).fold(JNull)(_.content)
          case other => other.getOrElse(JNull)
        acc :+ Decision(s(d, "action"), content, s(d, "chain"), s(d, "by"), s(d, "at"), s(d, "reason"),
          d("rejected").map(_.arr).getOrElse(Nil).flatMap(_.str).toList, s(d, "code"), s(d, "commit"), s(d, "tree"),
          d("held").map(_.arr).getOrElse(Nil).flatMap(_.str).toList, s(d, "after"), s(d, "key"), s(d, "sig"))
      }
    }.toMap)

  /** What `status` and the browser warn about the record itself: decisions committed earlier and
    * since rewritten, restarts of the ledger the developer has not acknowledged, and decisions of the
    * developer's not signed with a developer key (with no key yet, none is).
    */
  def warnings(root: Path, file: Path, now: Ledger): List[String] =
    rewrites(root, file, now).collect { case ("", why) => s"the ledger was rewritten: $why" } ++
      toAcknowledge(root, file, now).map((c, why) => s"$why in commit ${c.take(10)}: check what changed, then acknowledge it in the browser") ++
      Signing.untrusted(file.getParent.resolve("keys")).map(k => s"the key $k") ++
      Git.removed(root, root.relativize(file.getParent.resolve("keys")).toString).map((c, f) =>
        s"a developer key ($f) was removed in commit ${c.take(10)}: decisions it signed no longer count; restore it") ++
      (if now.decisions.nonEmpty && Signing.keys(file.getParent.resolve("keys")).isEmpty then
        List("no developer key: no decision counts until one signs it. Start the browser (`frflow serve`), which creates your key, commit .frflow/keys/, and sign the decisions there; CI should pin the key with FRFLOW_DEVELOPER_KEYS")
      else Nil) ++
      Signing.unsigned(now, file.getParent.resolve("keys")).map((id, d) =>
        s"$id: the ${d.action} of ${d.at} by ${d.by} is not signed by a developer key: decide it again in the browser, or sign it there if it is yours")

  /** Warnings when a committed version of the ledger, or the ledger now, changed or removed
    * decisions recorded in a version it follows (its parents in git; a merge keeps both sides'). The
    * ledger only grows. A commit that deletes it starts a new record, shown by `restarts`.
    */

  /** Commits that restarted or rewrote the ledger (a `git revert` of a decision rewrites it), with
    * what they did, that the developer has not acknowledged.
    */
  def toAcknowledge(root: Path, file: Path, now: Ledger): List[(String, String)] =
    (restarts(root, file).map(_ -> "the ledger was restarted") ++
      rewrites(root, file, now).collect { case (c, why) if c.nonEmpty => c -> s"the ledger was rewritten ($why)" })
      .filterNot((c, _) => now.acknowledged.exists(c.startsWith))
      .groupBy(_._1).toList.map((c, ws) => c -> ws.map(_._2).distinct.mkString("; "))

  /** Rewrites of committed decisions: (the commit that rewrote them, what), or ("", what) for the
    * ledger now, which is fixed rather than acknowledged.
    */
  def rewrites(root: Path, file: Path, now: Ledger): List[(String, String)] =
    val all = Git.versions(root, root.relativize(file).toString)
    val versions = all.drop(all.lastIndexWhere(_.text.isEmpty) + 1) // since the last restart
    def parse(t: String) = fromJson(Json.parse(t))
    val text = versions.map(v => v.commit -> v.text).toMap
    val committed = versions.flatMap { v =>
      v.text.toList.flatMap(t => v.parents.flatMap(text.get).flatten.flatMap(pt => rewrittenSince(parse(pt), parse(t))).map(v.commit -> _))
    }
    val head = versions.lastOption.flatMap(_.text).toList.flatMap(t => rewrittenSince(parse(t), now)).map("" -> _)
    (committed ++ head).distinct

  /** The commits that deleted the ledger: each started a new record, which could also hide a
    * rewrite. One the developer has not acknowledged (in the browser, with a reason) is a warning.
    */
  def restarts(root: Path, file: Path): List[String] =
    Git.versions(root, root.relativize(file).toString).collect { case v if v.text.isEmpty => v.commit }

  /** The id under which acknowledgements of the ledger itself are recorded. */
  val Self = "_ledger"

  /** Decisions present at an earlier version of the ledger (for example the committed one) that are
    * missing or different now: the ledger is append-only, so these mean it was rewritten.
    */
  def rewrittenSince(earlier: Ledger, now: Ledger): List[String] =
    // Every earlier decision is still there, in order (a merge may interleave both sides').
    def kept(ds: List[Decision], cur: List[Decision]): Boolean = ds match
      case Nil     => true
      case d :: tl => cur.dropWhile(_.unsigned != d.unsigned) match
        case Nil       => false
        case _ :: rest => kept(tl, rest)
    earlier.decisions.toList.sortBy(_._1).flatMap { (id, ds) =>
      if kept(ds, now.history(id)) then Nil else List(s"$id: decisions recorded earlier were changed or removed")
    }

/** Check results, derived from the model and Lean; kept in `.frflow/checks.json`, not committed. */
object Checks:
  private def s(j: Json, k: String): String = j(k).flatMap(_.str).getOrElse("")
  private def strs(j: Option[Json]) = j.map(_.arr).getOrElse(Nil).flatMap(_.str).toList

  def load(file: Path): Map[String, NodeCheck] =
    if !Files.isRegularFile(file) then Map.empty
    else Json.parse(Files.readString(file, UTF_8)).obj.map { (id, c) =>
      id -> NodeCheck(s(c, "hash"), s(c, "status"),
        c("obligations").map(_.arr).getOrElse(Nil).map(r => Result(s(r, "name"), s(r, "status"), s(r, "detail"))).toList,
        strs(c("messages")), strs(c("axioms")), s(c, "at"))
    }.toMap

  def save(file: Path, checks: Map[String, NodeCheck]): Unit =
    Files.createDirectories(file.getParent)
    Files.writeString(file, JObj(checks.toSeq.sortBy(_._1).map { (id, c) =>
      id -> obj("hash" -> str(c.hash), "status" -> str(c.status), "at" -> str(c.at),
        "obligations" -> JArr(c.obligations.map(r => obj("name" -> str(r.name), "status" -> str(r.status), "detail" -> str(r.detail)))),
        "messages" -> JArr(c.messages.map(str)), "axioms" -> JArr(c.axioms.map(str)))
    }).render() + "\n", UTF_8)
