package frflow.project.pipeline

import cats.data.NonEmptyChain
import frflow.core.analysis.Problem

/** Why a model is not analysed: the structural problems of the theory (a model is given elaborated, so what
  * elaboration refuses is the caller's to say). Raised (the caller cannot go on), so it extends `NoStackTrace`.
  */
enum Problems extends scala.util.control.NoStackTrace:
  case Invalid(problems: NonEmptyChain[Problem])
