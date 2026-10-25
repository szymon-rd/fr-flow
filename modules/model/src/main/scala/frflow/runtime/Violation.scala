package frflow
package runtime

/** What broke where the code runs: the contract, which check (`its check`, `the contract`, `the invariant I`, `the
  * assumption A`), the call's inputs, and the result (none when the values it runs with break an assumption).
  */
final case class Violation(contract: String, check: String, inputs: List[Any], result: Option[Any]):
  private def args = inputs.map(Example.show).mkString("(", ", ", ")")
  def message: String = result match
    case Some(r)                => s"$contract: result ${Example.show(r)} for $args breaks $check"
    case None if inputs.isEmpty => s"$contract: the values it starts with break $check"
    case None                   => s"$contract: the values it runs with break $check"
  /** One line with named fields, for logs to search and alert on. */
  def line: String =
    s"frflow contract violation: contract=$contract check=\"$check\" inputs=$args" + result.fold("")(r => s" result=${Example.show(r)}")

object Violation:
  /** The default report: the line, at ERROR, to the platform's logger named `frflow`. */
  val log: Violation => Unit = v => System.getLogger("frflow").log(System.Logger.Level.ERROR, v.line)
