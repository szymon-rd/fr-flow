package frflow
package ledger

import frflow.protocol.*
import io.circe.parser.decode
import io.circe.syntax.*
import java.nio.channels.FileChannel
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path, StandardCopyOption, StandardOpenOption}

/** Writing FrFlow's files: whole, then moved into place, so a reader never sees half a file. */
object Store:
  def write(file: Path, text: String): Unit =
    val dir = file.toAbsolutePath.getParent
    Files.createDirectories(dir)
    val tmp = Files.createTempFile(dir, s".${file.getFileName}", ".tmp")
    Files.writeString(tmp, text, UTF_8)
    Files.move(tmp, file, StandardCopyOption.REPLACE_EXISTING, StandardCopyOption.ATOMIC_MOVE)

  /** The file decoded, or `empty` when there is none; a file that does not read is an error. */
  def read[A: io.circe.Decoder](file: Path, empty: => A): A =
    if !Files.isRegularFile(file) then empty
    else decode[A](Files.readString(file, UTF_8)).fold(e => throw IllegalArgumentException(s"$file does not read: ${e.getMessage}"), identity)

  /** `f` with the lock file beside `file` held. */
  def locked[A](file: Path)(f: => A): A =
    Files.createDirectories(file.toAbsolutePath.getParent)
    val ch = FileChannel.open(file.resolveSibling(s"${file.getFileName}.lock"), StandardOpenOption.CREATE, StandardOpenOption.WRITE)
    try
      val lock = ch.lock()
      try f finally lock.release()
    finally ch.close()

/** The ledger in `.frflow/ledger.json`. */
object LedgerStore:
  def load(file: Path): Ledger = Store.read(file, Ledger.empty)
  def save(file: Path, l: Ledger): Unit = Store.write(file, Canonical.file(l.asJson) + "\n")

/** The developer's requests in `.frflow/requests.json`, and the agent's answers. */
object RequestStore:
  def load(file: Path): List[Request] = Store.read(file, List.empty[Request])

  /** Answers the request `to` with the text; given a node, the developer's open request on it, or a new
    * one from the agent. The file is locked while it is written. The id of the request answered.
    */
  def answer(file: Path, to: String, text: String, isNode: String => Boolean, now: java.time.Instant): Either[String, RequestId] =
    Store.locked(file) {
      val rs = load(file)
      val at = rs.indexWhere(_.id == RequestId(to)) match
        case -1 => rs.indexWhere(r => r.node.contains(NodeId(to)) && r.status == RequestStatus.Open)
        case i => i
      val all =
        if at >= 0 then Right(rs)
        else if !isNode(to) then Left(s"no request or node $to")
        else Right(rs :+ Request(RequestId(s"R${java.lang.Long.toString(now.toEpochMilli, 36)}"), Some(NodeId(to)), "(from the agent)",
          "agent", now.toString.take(19) + "Z", RequestStatus.Open))
      all.map { all =>
        val k = if at >= 0 then at else all.size - 1
        val answered = all(k).copy(status = RequestStatus.Answered, answer = Some(text))
        Store.write(file, Canonical.file(all.updated(k, answered).asJson) + "\n")
        answered.id
      }
    }
