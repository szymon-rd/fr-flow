package frflow.proof.layout

import frflow.core.analysis.Resolved
import frflow.proof.lean.ast.LeanModule

/** The modules of the vocabulary: `Types`, a `Def_` or `Term_` module per define and defined term, `Boundaries`. */
object VocabularyModules:
  def of(r: Resolved): List[LeanModule] = ???
