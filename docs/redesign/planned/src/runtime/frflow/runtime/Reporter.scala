package frflow.runtime

/** Where a running system reports a violation before throwing: a log line by default, a metric or an alert in an
  * application. The running system's configuration (`Running.make`), not the knowledge base's.
  */
trait Reporter:
  def report(v: Violation): Unit

object Reporter:
  /** One line to the platform logger named `frflow`. */
  val log: Reporter = v => System.getLogger("frflow").log(System.Logger.Level.ERROR, s"frflow contract violation: $v")
