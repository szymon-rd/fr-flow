package frflow
package check
package proving

import frflow.lean.*
import frflow.protocol.*

/** One run of Lean on one file, and what Lean said of it (see `Elaboration`). */
final case class Elaborated(run: Run, lean: Elaboration):
  /** A run that failed with no error in this file (an import that did not build, Lean stopped) checked nothing in it. */
  def verdict(name: ObligationName): TheoremVerdict = lean.verdict(name.lean) match
    case TheoremVerdict.Proven if !run.ok && !lean.diagnostics.exists(_.isError) =>
      TheoremVerdict.Failed("not checked: " + Verdict.quoted(run))
    case v => v
  def axiomsOf(name: ObligationName): Option[List[String]] = lean.axiomsOf(name.lean)
