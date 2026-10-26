package frflow.project.pipeline

import cats.data.NonEmptyChain
import frflow.core.analysis.Problem
import frflow.dsl.build.ElabError

/** Why a model is not analysed: what elaboration refused, or the structural problems of the theory. Raised (the
  * caller cannot go on), so it extends `NoStackTrace`.
  */
enum Problems extends scala.util.control.NoStackTrace:
  case NotElaborated(errors: NonEmptyChain[ElabError])
  case Invalid(problems: NonEmptyChain[Problem])
