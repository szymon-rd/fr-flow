package frflow
package check

import frflow.ledger.Json
import frflow.ledger.Json.*
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path}

/** Result of one obligation: `proven`, `open` or `failed`. A try (a statement Lean is asked whether it
  * can prove, see `Generate.tries`) has a plain status instead: the second of each pair when Lean proved
  * it, the first when it found no proof within the try's budget (which shows nothing): `needed` or
  * `not-needed` (a part, and `vacuous` with one part), `not-restates` or `restates` (one part),
  * `no-clash` or `clash`, `not-unsat` or `unsat`, `not-idle` or `idle`, `not-vacuous` or `vacuous` (an
  * expectation).
  */
final case class Result(name: String, status: String, detail: String = ""):
  /** A limit of what the node says, not an obligation: `idle` means doing nothing meets the root;
    * `restates`, that the node says what its one part says (a warning of `status`).
    */
  def isLimit: Boolean = name == "idle" || name == "restates"
  /** Lean evaluating an example as Scala does: the translation's cross-check. */
  def isEvaluation: Boolean = name.startsWith("eval") || name.startsWith("probe")
  /** Nothing to do about it: an obligation proven, a try that shows nothing wrong, or a limit. */
  def fine: Boolean = isLimit || Result.Fine(status)

object Result:
  /** The statuses that leave nothing to do: an obligation proven, a try showing nothing wrong. */
  val Fine: Set[String] = Set("proven", "needed", "not-restates", "no-clash", "not-unsat", "not-idle", "not-vacuous")


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

/** Check results, derived from the model and Lean; kept in `.frflow/checks.json`, not committed. */
object Checks:
  import Json.text as s
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
