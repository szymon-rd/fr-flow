package frflow
package vocabulary

/** `forall` and `exists` say something of every value: Scala cannot compute them, so running one throws this. */
final class NotExecutable(what: String) extends RuntimeException(s"$what cannot be executed")
