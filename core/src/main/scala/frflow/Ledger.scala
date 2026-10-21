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

/** An option the developer did not choose: the node as it was proposed. */
final case class Alternative(id: String, content: Json):
  def statement: String = content("statement").flatMap(_.str).getOrElse("")
  def why: String = content("why").flatMap(_.str).getOrElse("")

/** A decision of the developer about a node.
  *
  * @param action   `accept`, or `remove` (the node was deleted from the model)
  * @param content  the node as the developer saw it when deciding; its hash is what the decision is bound to
  * @param chain    the decided content of the ancestors; when it changes, the decision must be confirmed
  * @param reason   why the developer chose it
  * @param rejected the alternatives not chosen, as they were proposed
  * @param code     the fingerprint of the source files the node governs, when decided
  */
final case class Decision(action: String, content: Json, chain: String, by: String, at: String, reason: String,
    rejected: List[Alternative], code: String = ""):
  def hash: String = Decision.hash(content)

object Decision:
  def hash(content: Json): String =
    java.security.MessageDigest.getInstance("SHA-256").digest(content.compact.getBytes(UTF_8)).map("%02x".format(_)).mkString

/** The developer's decisions, per node, oldest first: the record of the theory.
  * Kept in `.frflow/ledger.json` and committed. Nothing in it is ever overwritten.
  */
final case class Ledger(decisions: Map[String, List[Decision]]):
  def history(id: String): List[Decision] = decisions.getOrElse(id, Nil)
  def current(id: String): Option[Decision] = history(id).lastOption
  def add(id: String, d: Decision): Ledger = Ledger(decisions.updated(id, history(id) :+ d))

  /** Every alternative ever rejected for a node, latest version of each. */
  def rejected(id: String): List[Alternative] =
    history(id).flatMap(_.rejected).foldLeft(List.empty[Alternative])((acc, a) => acc.filterNot(_.id == a.id) :+ a)

  def toJson: Json =
    obj("decisions" -> JObj(decisions.toSeq.sortBy(_._1).map { (id, ds) =>
      id -> JArr(ds.map(d => obj(
        "action" -> str(d.action), "by" -> str(d.by), "at" -> str(d.at), "reason" -> str(d.reason),
        "rejected" -> JArr(d.rejected.map(a => obj("id" -> str(a.id), "content" -> a.content))),
        "chain" -> str(d.chain), "code" -> str(d.code), "content" -> d.content
      )))
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
      id -> ds.arr.map(d => Decision(s(d, "action"), d("content").getOrElse(JNull), s(d, "chain"), s(d, "by"), s(d, "at"), s(d, "reason"),
        d("rejected").map(_.arr).getOrElse(Nil).map(a => Alternative(s(a, "id"), a("content").getOrElse(JNull))).toList,
        s(d, "code"))).toList
    }.toMap)

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
