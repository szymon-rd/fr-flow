package frflow.wire.file

/** Why a file did not read, naming the file: it is not JSON, it has no version, its version is not the one this
  * FrFlow reads, or a field (its path in the file, `.decisions.Root[0].action`) does not read at that version.
  */
enum Unreadable:
  case NotJson(file: String, problem: String)
  case NoVersion(file: String)
  case UnknownVersion(file: String, version: Int, reads: Int)
  case BadField(file: String, version: Int, field: String, problem: String)

  def file: String
