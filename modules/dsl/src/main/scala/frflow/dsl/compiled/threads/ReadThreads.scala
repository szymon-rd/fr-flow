package frflow.dsl.compiled.threads

import frflow.core.threads.Draft
import frflow.dsl.compiled.threads.known.ThreadUnit
import scala.quoted.Quotes

/** Compiled Scala read as thread programs: the classes and methods a unit names, read from their TASTy (`q`: the
  * trees of the place they were compiled into, `compiled.Inspect`) into the language of
  * `modules/proof/rocq/FrFlow/Threads/Lang.v`, by rules over Scala's constructs
  * (`docs/THREADS-GENERATOR.md`). `core.threads.Assemble` lays the result out as a file, and
  * `proof.rocq.threads` prints it.
  */
object ReadThreads:
  def apply(q: Quotes, unit: ThreadUnit): Draft = Reader(q, unit).draft

/** The reader, each part a rule or a few. */
private final class Reader(val q: Quotes, val unit: ThreadUnit) extends ReadClasses
