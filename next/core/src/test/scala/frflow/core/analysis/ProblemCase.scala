package frflow.core.analysis

import frflow.core.Kb

/** A theory with one thing wrong, and every problem `Validate` reports for it: each of one kind, named `name`. */
final case class ProblemCase(kb: Kb, expected: List[Problem]):
  def name: String = expected.headOption.fold("none")(_.productPrefix)
