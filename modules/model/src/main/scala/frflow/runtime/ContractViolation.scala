package frflow
package runtime

/** Raised where a result or a value breaks what was decided, after the violation is reported: the result is never
  * returned (fail closed). An application maps it to its own failure (an HTTP layer, to a 500).
  */
final class ContractViolation(val violation: Violation) extends RuntimeException(violation.message)
