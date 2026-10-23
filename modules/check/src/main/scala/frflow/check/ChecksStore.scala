package frflow
package check

import cats.effect.IO
import frflow.ledger.Store
import frflow.protocol.*
import io.circe.Json
import io.circe.parser.decode
import io.circe.syntax.*
import java.nio.file.Path

/** Check results, derived from the model and Lean; kept in `.frflow/checks.json`, not committed. */
final case class ChecksStore(file: Path):
  /** The recorded checks; none when the file is missing, or written by another version (all are checked again). */
  def load: IO[Map[NodeId, NodeCheck]] =
    Disk.read(file).map(_.flatMap(decode[Map[NodeId, NodeCheck]](_).toOption).getOrElse(Map.empty))

  def save(checks: Map[NodeId, NodeCheck]): IO[Unit] = Store.write(file, ChecksStore.print(checks))

object ChecksStore:
  def print(checks: Map[NodeId, NodeCheck]): String =
    Canonical.file(Json.fromFields(checks.toList.sortBy(_._1).map((id, c) => id.value -> c.asJson))) + "\n"
