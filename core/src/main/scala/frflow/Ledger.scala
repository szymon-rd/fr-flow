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
  * @param action   `accept` (the developer chose the node, as seen), `confirm` (it still holds after
  *                 something above it or its code moved), `reject` (an alternative not chosen, as it
  *                 was proposed), `revisit` (the developer said a change above may affect it, so it is
  *                 reviewed again) or `remove` (the developer agreed that a decided node is gone)
  * @param content  the node as the developer saw it; the decision is bound to its hash
  * @param chain    the content of the ancestors, as decided; when it changes, the node is reviewed
  * @param reason   why: kept as part of the theory
  * @param rejected for `accept`, the alternatives rejected by this choice
  * @param code     the fingerprint of the source files the node governs, when decided
  * @param commit   the code as decided, written to git (a tree; older entries hold the commit then
  *                 checked out), to show how the code changed since
  */
final case class Decision(action: String, content: Json, chain: String, by: String, at: String, reason: String,
    rejected: List[String] = Nil, code: String = "", commit: String = ""):
  def hash: String = Decision.hash(content)

object Decision:
  def hash(content: Json): String =
    java.security.MessageDigest.getInstance("SHA-256").digest(content.compact.getBytes(UTF_8)).map("%02x".format(_)).mkString

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
    history(id).reverse.takeWhile(d => d.action != "reject" && d.action != "remove").reverse.find(_.action == "accept")
  /** What the node is bound to now: its last acceptance or confirmation (also while the developer
    * has asked to revisit it).
    */
  def binding(id: String): Option[Decision] = current(id) match
    case Some(d) if d.action == "revisit" => history(id).reverse.find(x => x.action == "accept" || x.action == "confirm")
    case c => c.filter(d => d.action == "accept" || d.action == "confirm")
  def add(id: String, d: Decision): Ledger = Ledger(decisions.updated(id, history(id) :+ d))

  /** The alternatives ever rejected in favour of a node, as they were proposed. */
  def alternatives(id: String): List[(String, Json)] =
    history(id).filter(_.action == "accept").flatMap(_.rejected).distinct
      .flatMap(r => history(r).reverse.find(_.action == "reject").map(d => r -> d.content))

  /** Every decision, newest first. */
  def all: List[(String, Decision)] = decisions.toList.flatMap((id, ds) => ds.map(id -> _)).sortBy(_._2.at).reverse

  /** Content repeated from the node's previous decision is written once ("content": "same"). */
  def toJson: Json =
    obj("decisions" -> JObj(decisions.toSeq.sortBy(_._1).map { (id, ds) =>
      id -> JArr(ds.zipWithIndex.map((d, i) => JObj(Seq(
        "action" -> str(d.action), "by" -> str(d.by), "at" -> str(d.at), "reason" -> str(d.reason)) ++
        (if d.rejected.isEmpty then Nil else Seq("rejected" -> JArr(d.rejected.map(str)))) ++
        (if d.code.isEmpty then Nil else Seq("code" -> str(d.code))) ++
        (if d.commit.isEmpty then Nil else Seq("commit" -> str(d.commit))) ++
        Seq("chain" -> str(d.chain), "content" -> (if i > 0 && ds(i - 1).content == d.content then str("same") else d.content)))))
    }))

object Ledger:
  val empty: Ledger = Ledger(Map.empty)

  def load(file: Path): Ledger =
    if !Files.isRegularFile(file) then empty else fromJson(Json.parse(Files.readString(file, UTF_8)))

  def save(file: Path, l: Ledger): Unit =
    Files.createDirectories(file.getParent)
    Files.writeString(file, l.toJson.render() + "\n", UTF_8)

  private def s(j: Json, k: String): String = j(k).flatMap(_.str).getOrElse("")

  def fromJson(j: Json): Ledger =
    Ledger(j("decisions").map(_.obj).getOrElse(Nil).map { (id, ds) =>
      id -> ds.arr.foldLeft(List.empty[Decision]) { (acc, d) =>
        val content = d("content") match
          case Some(JStr("same")) => acc.lastOption.fold(JNull)(_.content)
          case other              => other.getOrElse(JNull)
        acc :+ Decision(s(d, "action"), content, s(d, "chain"), s(d, "by"), s(d, "at"), s(d, "reason"),
          d("rejected").map(_.arr).getOrElse(Nil).flatMap(_.str).toList, s(d, "code"), s(d, "commit"))
      }
    }.toMap)

  /** Warnings when any committed version of the ledger, or the ledger now, changed or removed
    * decisions recorded in the version before it: the ledger only grows. A commit that deletes the
    * ledger starts a new record, visibly, in git.
    */
  def rewrites(root: Path, file: Path, now: Ledger): List[String] =
    val versions = Git.versions(root, root.relativize(file).toString)
    val committed = versions.drop(versions.lastIndexOf(None) + 1).flatten.map(t => fromJson(Json.parse(t)))
    (committed :+ now).sliding(2).toList.flatMap {
      case List(before, after) => rewrittenSince(before, after)
      case _                   => Nil
    }.distinct.map("the ledger was rewritten: " + _)

  /** Decisions present at an earlier version of the ledger (for example the committed one) that are
    * missing or different now: the ledger is append-only, so these mean it was rewritten.
    */
  def rewrittenSince(earlier: Ledger, now: Ledger): List[String] =
    earlier.decisions.toList.sortBy(_._1).flatMap { (id, ds) =>
      val cur = now.history(id)
      if cur.take(ds.size) == ds then Nil else List(s"$id: decisions recorded earlier were changed or removed")
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
