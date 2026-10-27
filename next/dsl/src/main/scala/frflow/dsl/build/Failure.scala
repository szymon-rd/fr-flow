package frflow.dsl.build

/** A fault found inside the developer's lambda (by `forall`, `filter`, … which must return a term at once), caught by
  * `Elab.guarded`, which knows the site.
  */
final class Failure(val fault: Fault) extends RuntimeException(null, null, false, false)
