package frflow
package ledger
package store

import java.nio.file.Path
import scala.util.control.NoStackTrace

/** What fails reading or writing the ledger module's files: raised in `IO`, mapped once at each edge. */
enum LedgerError(message: String) extends Exception(message) with NoStackTrace:
  /** FrFlow does not guess what the file held. */
  case BadFile(path: Path, reason: String) extends LedgerError(s"$path does not read: $reason")
  case BadKey(path: Path, reason: String) extends LedgerError(s"the signing key $path does not read: $reason")
