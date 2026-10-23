package frflow
package check

import frflow.ledger.Store
import frflow.protocol.*
import io.circe.Json
import io.circe.parser.decode
import io.circe.syntax.*
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path}

/** Check results, derived from the model and Lean; kept in `.frflow/checks.json`, not committed. */
object Checks:
  /** The recorded checks; none when the file is missing, or written by another version (all are checked again). */
  def load(file: Path): Map[NodeId, NodeCheck] =
    if !Files.isRegularFile(file) then Map.empty
    else decode[Map[NodeId, NodeCheck]](Files.readString(file, UTF_8)).getOrElse(Map.empty)

  def save(file: Path, checks: Map[NodeId, NodeCheck]): Unit =
    Store.write(file, Canonical.file(Json.fromFields(checks.toList.sortBy(_._1).map((id, c) => id.value -> c.asJson))) + "\n")
