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

/** An option the developer did not choose, kept as part of the theory. */
final case class Alternative(id: String, hash: String, statement: String, why: String)

/** The developer's decision to accept a node.
  *
  * @param hash     what was decided: the node's statement, reason, sources, examples and Lean
  * @param chain    the decided state of its ancestors; when they change, the decision must be confirmed
  * @param note     the developer's reason for the choice
  * @param content  the node as it was decided, to show what changed since
  * @param rejected the alternatives proposed with it and not chosen
  */
final case class Decision(hash: String, chain: String, by: String, at: String, note: String, content: Json, rejected: List[Alternative])

final case class LedgerEntry(decision: Option[Decision], check: Option[NodeCheck])

/** Approvals and check results of every node, kept in `.frflow/ledger.json`. */
final case class Ledger(nodes: Map[String, LedgerEntry]):
  def entry(id: String): LedgerEntry = nodes.getOrElse(id, LedgerEntry(None, None))
  def updated(id: String)(f: LedgerEntry => LedgerEntry): Ledger = copy(nodes = nodes.updated(id, f(entry(id))))

  def toJson: Json =
    def results(rs: List[Result]) = JArr(rs.map(r => obj("name" -> str(r.name), "status" -> str(r.status), "detail" -> str(r.detail))))
    obj("nodes" -> JObj(nodes.toSeq.sortBy(_._1).map { (id, e) =>
      id -> JObj(
        e.decision.toSeq.map(d => "decision" -> obj(
          "hash" -> str(d.hash), "chain" -> str(d.chain), "by" -> str(d.by), "at" -> str(d.at), "note" -> str(d.note),
          "rejected" -> JArr(d.rejected.map(a => obj("id" -> str(a.id), "hash" -> str(a.hash), "statement" -> str(a.statement), "why" -> str(a.why)))),
          "content" -> d.content
        )) ++
          e.check.toSeq.map(c =>
            "check" -> obj(
              "hash" -> str(c.hash), "status" -> str(c.status), "at" -> str(c.at),
              "obligations" -> results(c.obligations),
              "messages" -> JArr(c.messages.map(str)), "axioms" -> JArr(c.axioms.map(str))
            )
          )
      )
    }))

object Ledger:
  val empty: Ledger = Ledger(Map.empty)

  def load(file: Path): Ledger =
    if !Files.isRegularFile(file) then empty else fromJson(Json.parse(Files.readString(file, UTF_8)))

  def save(file: Path, l: Ledger): Unit =
    Files.createDirectories(file.getParent)
    Files.writeString(file, l.toJson.render() + "\n", UTF_8)

  private def s(j: Json, k: String): String = j(k).flatMap(_.str).getOrElse("")
  private def results(j: Option[Json]): List[Result] =
    j.map(_.arr).getOrElse(Nil).map(r => Result(s(r, "name"), s(r, "status"), s(r, "detail"))).toList

  def fromJson(j: Json): Ledger =
    Ledger(j("nodes").map(_.obj).getOrElse(Nil).map { (id, e) =>
      id -> LedgerEntry(
        e("decision").map(d => Decision(s(d, "hash"), s(d, "chain"), s(d, "by"), s(d, "at"), s(d, "note"), d("content").getOrElse(JNull),
          d("rejected").map(_.arr).getOrElse(Nil).map(a => Alternative(s(a, "id"), s(a, "hash"), s(a, "statement"), s(a, "why"))).toList)),
        e("check").map(c =>
          NodeCheck(
            s(c, "hash"), s(c, "status"), results(c("obligations")),
            c("messages").map(_.arr).getOrElse(Nil).flatMap(_.str).toList,
            c("axioms").map(_.arr).getOrElse(Nil).flatMap(_.str).toList, s(c, "at")
          )
        )
      )
    }.toMap)
