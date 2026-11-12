package frflow.dsl.compiled.threads

import frflow.dsl.compiled.threads.known.ThreadUnit
import scala.quoted.Quotes

/** The reader of thread programs: its parts, each a rule or a few of `docs/THREADS-GENERATOR.md`, over the trees of
  * `q` and the unit `unit`.
  */
private[threads] final class Reader(val q: Quotes, val unit: ThreadUnit) extends ReadClasses
