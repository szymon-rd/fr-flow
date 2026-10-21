package frflow.ledger

import frflow.json.Json
import frflow.json.Json.*
import frflow.workspace.{Files2, Workspace}
import java.nio.file.Path

enum Verification:
  case NotChecked, ModelError, Failed, Open, Discharged, Proven

  def label: String = this match
    case NotChecked => "not-checked"
    case ModelError => "model-error"
    case Failed     => "failed"
    case Open       => "open"
    case Discharged => "discharged"
    case Proven     => "proven"

object Verification:
  def fromLabel(s: String): Verification = values.find(_.label == s).getOrElse(NotChecked)

enum ObligationStatus:
  case Proven, Open, Failed
  def label: String = toString.toLowerCase

object ObligationStatus:
  def fromLabel(s: String): ObligationStatus = values.find(_.label == s).getOrElse(Open)

final case class ObligationResult(name: String, status: ObligationStatus, detail: String = "")

/** A human approval of a node's statement and model, bound to its spec hash. */
final case class Approval(specHash: String, by: String, at: String)

final case class CheckRecord(
    checkHash: String,
    verification: Verification,
    obligations: Seq[ObligationResult],
    axioms: Map[String, Seq[String]],
    messages: Seq[String],
    checkedAt: String
)

final case class NodeEntry(approval: Option[Approval], lastCheck: Option[CheckRecord])

final case class Ledger(nodes: Map[String, NodeEntry]):
  def entry(id: String): NodeEntry = nodes.getOrElse(id, NodeEntry(None, None))
  def updated(id: String)(f: NodeEntry => NodeEntry): Ledger = copy(nodes = nodes.updated(id, f(entry(id))))

  def toJson: Json =
    JObj(Seq("version" -> JNum(1), "nodes" -> JObj(nodes.toSeq.sortBy(_._1).map((id, e) => id -> Ledger.entryJson(e)))))

object Ledger:
  val empty: Ledger = Ledger(Map.empty)

  def load(ws: Workspace): Ledger = Files2.read(ws.ledgerFile).fold(empty)(s => fromJson(Json.parse(s)))

  def save(ws: Workspace, ledger: Ledger): Path =
    Files2.writeIfChanged(ws.ledgerFile, ledger.toJson.render() + "\n")
    ws.ledgerFile

  private def entryJson(e: NodeEntry): Json =
    JObj(
      e.approval.toSeq.map(a =>
        "approval" -> obj("specHash" -> str(a.specHash), "by" -> str(a.by), "at" -> str(a.at))
      ) ++ e.lastCheck.toSeq.map(c =>
        "lastCheck" -> obj(
          "checkHash" -> str(c.checkHash),
          "verification" -> str(c.verification.label),
          "checkedAt" -> str(c.checkedAt),
          "obligations" -> JArr(c.obligations.map(o =>
            obj("name" -> str(o.name), "status" -> str(o.status.label), "detail" -> str(o.detail))
          )),
          "axioms" -> JObj(c.axioms.toSeq.sortBy(_._1).map((k, v) => k -> JArr(v.sorted.map(str)))),
          "messages" -> JArr(c.messages.map(str))
        )
      )
    )

  def fromJson(j: Json): Ledger =
    val nodes = j("nodes").map(_.obj).getOrElse(Nil).map { (id, e) =>
      val approval = e("approval").map { a =>
        Approval(
          a("specHash").flatMap(_.str).getOrElse(""),
          a("by").flatMap(_.str).getOrElse(""),
          a("at").flatMap(_.str).getOrElse("")
        )
      }
      val check = e("lastCheck").map { c =>
        CheckRecord(
          checkHash = c("checkHash").flatMap(_.str).getOrElse(""),
          verification = Verification.fromLabel(c("verification").flatMap(_.str).getOrElse("")),
          obligations = c("obligations").map(_.arr).getOrElse(Nil).map { o =>
            ObligationResult(
              o("name").flatMap(_.str).getOrElse(""),
              ObligationStatus.fromLabel(o("status").flatMap(_.str).getOrElse("")),
              o("detail").flatMap(_.str).getOrElse("")
            )
          },
          axioms = c("axioms").map(_.obj).getOrElse(Nil).map((k, v) => k -> v.arr.flatMap(_.str)).toMap,
          messages = c("messages").map(_.arr).getOrElse(Nil).flatMap(_.str),
          checkedAt = c("checkedAt").flatMap(_.str).getOrElse("")
        )
      }
      id -> NodeEntry(approval, check)
    }
    Ledger(nodes.toMap)
