package frflow
package lean
package reading

final case class Diagnostic(file: String, line: Int, severity: Severity, message: String):
  def isError: Boolean = severity == Severity.Error
  def isSorry: Boolean = severity == Severity.Warning && message.contains("declaration uses")
