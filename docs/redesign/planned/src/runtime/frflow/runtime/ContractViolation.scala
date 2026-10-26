package frflow.runtime

/** Thrown by a service after reporting a result that breaks its contract. */
final class ContractViolation(val violation: Violation) extends RuntimeException(violation.toString, null, false, false)
