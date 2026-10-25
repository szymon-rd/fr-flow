package frflow
package node

/** An implementation of a boundary, started in a model's state (`start`) and read back (`read`): an outside system
  * (`outside`: a database; its model stays assumed) or code of the project's own (tested against the model). `source`
  * is how it is started, as written; `files`, the project files that expression refers to (the model's file last).
  */
final case class ModelImpl(start: Any => Any, read: Any => Any, outside: Boolean, source: String, files: List[String]):
  def sources: List[String] = files.dropRight(1)
