package frflow.dsl.model

import frflow.dsl.term.Term

/** A fact about the world outside the code, said of a model (`stored.onlyCodeChanges`, `stored.atomic`,
  * `stored.initially(…)`, owner §16, §36): what an assumption says whole, and nothing else takes. It is no term, so
  * it is never a part of a formula (`!stored.atomic` and `stored.atomic implies p` do not compile), and no claim
  * says one (`Node.claim` takes a term only).
  */
final class Fact private[dsl] (private[dsl] val term: Term[Boolean])
